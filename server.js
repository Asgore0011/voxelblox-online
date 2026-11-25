#!/usr/bin/env node
// Собрано из offline-server.js приложения VoxelBlox. Запуск: npm install && npm start
process.env.STORAGE = process.env.STORAGE || 'json';
'use strict';
// VoxelBlox сервер v3: раздаёт игру, серверная авторизация, аккаунты/плейсы (data.json), мультиплеер в комнатах.
//
// Безопасность (всё проверяется на сервере, клиенту не доверяем):
//  - пароли: scrypt + индивидуальная соль, сравнение за постоянное время; пароль не хранится и не логируется
//  - сессии: случайный 256-битный токен, в базе хранится только его SHA-256, срок жизни 30 дней
//  - права: аккаунты закрыты полностью; плейсы может менять/удалять только владелец; магазин и монеты считает сервер
//  - лимиты: попытки входа по IP и по нику, регистрации по IP, скорость сообщений, размер данных, соединения с одного IP
//  - данные плейсов проверяются и очищаются (структура, размеры, цвета, числа), имена/чат — от управляющих символов
//  - имя и одежда игрока в мультиплеере берутся из аккаунта на сервере — подделать нельзя
//
// Переменные окружения: PORT, DATA_DIR, TRUST_PROXY (число прокси перед сервером), REQUIRE_HTTPS=1,
//   ALLOWED_ORIGINS (через запятую, если игра открывается с другого домена), MAX_ROOM, MAX_CONN, MAX_CONN_IP.
//   Почта (привязка e-mail и восстановление пароля): SMTP_HOST, SMTP_PORT (465 или 587), SMTP_USER, SMTP_PASS, SMTP_FROM.
//   Без SMTP_HOST коды из писем печатаются в консоль сервера (удобно для локальной игры).
const http = require('http'), fs = require('fs'), path = require('path'), crypto = require('crypto'), net = require('net'), tls = require('tls');
let WebSocketServer;
try { ({ WebSocketServer } = require('ws')) } catch { ({ WebSocketServer } = require('./vendor/ws')) }   // нужен пакет ws: npm install

// ===================== настройки =====================
const PORT = process.env.PORT || 3000;
const DATA_DIR = process.env.DATA_DIR || __dirname;
try { fs.mkdirSync(DATA_DIR, { recursive: true }) } catch { }
const FILE = path.join(DATA_DIR, 'data.json');
const PUB = path.join(__dirname, 'public');
const REQUIRE_HTTPS = process.env.REQUIRE_HTTPS === '1';
const MAX_ROOM = +process.env.MAX_ROOM || 10;   // игроков на одном сервере (ОШИБКА 416, если сервер полон)
const MAX_CONN = +process.env.MAX_CONN || 5000;
const MAX_CONN_IP = +process.env.MAX_CONN_IP || 30;
const SESSION_MS = 30 * 864e5;
const MAX_SESSIONS_PER_USER = 10;
const MAX_PLACES_PER_USER = 30;
const MAX_OBJS = 1500, MAX_SCRIPTS = 20, MAX_LUA = 50000, MAX_SRC = 120000, MAX_CONTENT = 2600000, MAX_AUDIO = 1600000;
const ICON_RE = /^data:image\/(jpeg|png|webp);base64,([A-Za-z0-9+\/]+={0,2})$/, AUDIO_RE = /^data:audio\/[a-z0-9.+-]+;base64,[A-Za-z0-9+\/]+={0,2}$/i;
const ALLOWED_ORIGINS = (process.env.ALLOWED_ORIGINS || '').split(',').map(s => s.trim().toLowerCase()).filter(Boolean);
// TRUST_PROXY: сколько прокси стоит перед сервером (Render/Railway/Fly = 1, Cloudflare + платформа = 2).
// Не задано — доверяем X-Forwarded-For только если соединение пришло с локальной/частной сети.
const TRUST_HOPS = process.env.TRUST_PROXY == null || process.env.TRUST_PROXY === '' ? null
  : process.env.TRUST_PROXY === 'true' ? 1 : Math.max(0, parseInt(process.env.TRUST_PROXY, 10) || 0);

const log = (...a) => console.log(new Date().toISOString(), ...a);
class Err extends Error { constructor(msg, code) { super(msg); this.code = code } }
const sha = s => crypto.createHash('sha256').update(s).digest('hex');
const nul = () => Object.create(null);   // объекты без прототипа: ник "__proto__" не сломает сервер
const EMAIL_RE = /^[A-Za-z0-9._%+\-]{1,64}@[A-Za-z0-9](?:[A-Za-z0-9\-]{0,61}[A-Za-z0-9])?(?:\.[A-Za-z0-9](?:[A-Za-z0-9\-]{0,61}[A-Za-z0-9])?)*\.[A-Za-z]{2,24}$/;
const EMAILS = new Map();   // подтверждённая почта -> ключ аккаунта (одна почта = один аккаунт)

// ===================== магазин (цены — только на сервере) =====================
const SHOP = [['sh', null, 0], ['sh', '#e74c3c', 50], ['sh', '#3498db', 50], ['sh', '#2ecc71', 50], ['sh', '#f1c40f', 60], ['sh', '#9b59b6', 80], ['sh', '#222222', 80],
  ['hat', null, 0], ['hat', 'cube', 150], ['hat', 'tall', 200], ['hat', 'crown', 500]];
const shopItem = (k, val) => SHOP.find(i => i[0] === k && i[1] === val) || null;
const shopKey = (k, val) => k + ':' + val;
// ===================== яйца (шансы и цена — только на сервере) =====================
const EGG = { price: 250, pets: [
  { id: 'cat', n: 'Cube Cat', e: '🐱', r: 'Common', w: 35 }, { id: 'slime', n: 'Slime', e: '🟢', r: 'Common', w: 25 },
  { id: 'fox', n: 'Fox', e: '🦊', r: 'Uncommon', w: 15 }, { id: 'owl', n: 'Owl', e: '🦉', r: 'Rare', w: 10 },
  { id: 'phx', n: 'Phoenix', e: '🔥', r: 'Epic', w: 10 }, { id: 'dragon', n: 'Dragon', e: '🐲', r: 'Legendary', w: 5 }] };
const EGG_IDS = new Set(EGG.pets.map(p => p.id)), EGG_W = EGG.pets.reduce((s, p) => s + p.w, 0);
function rollPet() { let x = crypto.randomInt(EGG_W); for (const p of EGG.pets) { if (x < p.w) return p; x -= p.w } return EGG.pets[0] }

const UKEY = /^u:[a-z0-9]{6,24}$/, OWN_FREE = Object.create(null);   // OWN_FREE: заполняется своими вещами (бесплатно для автора)
const SHOP_KEYS = new Set(SHOP.filter(i => i[2] > 0).map(i => shopKey(i[0], i[1])));

// ===================== очистка текста =====================
const BAD_CHARS = new RegExp('[\\u0000-\\u001f\\u007f-\\u009f\\u200b-\\u200f\\u2028-\\u202e\\u2060-\\u206f\\ufeff\\ufff9-\\ufffb]', 'g');
function clean(s, max) {
  if (typeof s !== 'string') return '';
  s = s.normalize('NFC').replace(BAD_CHARS, '').replace(/\s+/g, ' ').trim();
  return Array.from(s).slice(0, max).join('').trim();
}

// ===================== база данных =====================
let DB = { accounts: nul(), places: nul(), sessions: nul(), items: nul(), assets: nul(), reports: [] };

function toNul(src) { const o = nul(); if (src && typeof src === 'object') for (const k of Object.keys(src)) o[k] = src[k]; return o }

// ===== хранилище: SQLite (node:sqlite, Node >= 22.13) или запасной JSON-файл (STORAGE=json) =====
let sqlite = null;
if (process.env.STORAGE !== 'json') { try { sqlite = new (require('node:sqlite').DatabaseSync)(path.join(DATA_DIR, 'blockverse.db')) } catch (e) { log('SQLite недоступен (' + e.message + '). Нужен Node.js 22.13+. Использую data.json.') } }
function loadJsonFile(f) { return JSON.parse(fs.readFileSync(f, 'utf8')) }
function readJsonDB() {
  if (!fs.existsSync(FILE)) return null;
  try { return loadJsonFile(FILE) } catch (e) {
    log('ОШИБКА: data.json повреждён:', e.message);
    try { const r = loadJsonFile(FILE + '.bak'); log('Загружена резервная копия data.json.bak'); return r } catch (e2) {
      log('Резервная копия тоже недоступна. Сервер остановлен, чтобы не затереть данные. Проверь', FILE); process.exit(1);
    }
  }
}
function loadDB() {
  let raw = null;
  if (sqlite) {
    sqlite.exec('PRAGMA journal_mode=WAL; PRAGMA synchronous=NORMAL; CREATE TABLE IF NOT EXISTS accounts(k TEXT PRIMARY KEY, data TEXT NOT NULL); CREATE TABLE IF NOT EXISTS items(k TEXT PRIMARY KEY, data TEXT NOT NULL); CREATE TABLE IF NOT EXISTS places(k TEXT PRIMARY KEY, owner TEXT, data TEXT NOT NULL); CREATE TABLE IF NOT EXISTS sessions(k TEXT PRIMARY KEY, data TEXT NOT NULL); CREATE TABLE IF NOT EXISTS assets(k TEXT PRIMARY KEY, data TEXT NOT NULL);');
    const rows = t => sqlite.prepare('SELECT k, data FROM ' + t).all();
    const acc = rows('accounts');
    if (!acc.length && !rows('places').length) {            // первый запуск: переносим старый data.json
      const old = readJsonDB();
      if (old) { raw = old; migrateToSqlite(old); try { fs.renameSync(FILE, FILE + '.migrated') } catch { } log('data.json перенесён в SQLite (файл переименован в data.json.migrated)') }
    } else {
      raw = { accounts: {}, places: {}, sessions: {}, items: {}, assets: {} };
      for (const r of rows('assets')) { try { raw.assets[r.k] = JSON.parse(r.data) } catch { } }
      for (const r of rows('items')) { try { raw.items[r.k] = JSON.parse(r.data) } catch { } }
      for (const r of acc) { try { raw.accounts[r.k] = JSON.parse(r.data) } catch { } }
      for (const r of rows('places')) { try { raw.places[r.k] = JSON.parse(r.data) } catch { } }
      for (const r of rows('sessions')) { try { raw.sessions[r.k] = JSON.parse(r.data) } catch { } }
    }
  } else raw = readJsonDB();
  if (!raw || typeof raw !== 'object') return;
  DB.accounts = toNul(raw.accounts); DB.places = toNul(raw.places); DB.sessions = toNul(raw.sessions); DB.items = toNul(raw.items); DB.assets = toNul(raw.assets || {}); DB.reports = Array.isArray(raw.reports) ? raw.reports.slice(-500) : [];
}
function migrateToSqlite(old) {   // сохраняем «как есть»; нормализация произойдёт при загрузке и запишется при следующем изменении
  sqlite.exec('BEGIN');
  const a = sqlite.prepare('INSERT OR REPLACE INTO accounts(k,data) VALUES(?,?)'), p = sqlite.prepare('INSERT OR REPLACE INTO places(k,owner,data) VALUES(?,?,?)'), q = sqlite.prepare('INSERT OR REPLACE INTO sessions(k,data) VALUES(?,?)');
  for (const k of Object.keys(old.accounts || {})) a.run(k, JSON.stringify(old.accounts[k]));
  for (const k of Object.keys(old.places || {})) { const v = old.places[k]; p.run(k, String(v && v.owner || ''), JSON.stringify(v)) }
  for (const k of Object.keys(old.sessions || {})) q.run(k, JSON.stringify(old.sessions[k]));
  sqlite.exec('COMMIT');
}
loadDB();

// --- нормализация старых данных (аккаунты/плейсы из прошлых версий) ---
const SKEL_MAP = { 'а': 'a', 'в': 'b', 'е': 'e', 'ё': 'e', 'к': 'k', 'м': 'm', 'н': 'h', 'о': 'o', 'р': 'p', 'с': 'c', 'т': 't', 'у': 'y', 'х': 'x', '0': 'o', '1': 'l', 'i': 'l', '_': '' };
const skeleton = n => Array.from(String(n).toLowerCase()).map(c => c in SKEL_MAP ? SKEL_MAP[c] : c).join('');
const RESERVED = new Set(['admin', 'administrator', 'moderator', 'mod', 'system', 'server', 'root', 'blockverse', 'voxelblox', 'staff', 'support', 'owner', 'official', 'bot', 'null', 'undefined', 'guest', 'voxelblox'].map(skeleton));
const SKEL = new Map(); // skeleton -> ключ аккаунта (защита от двойников: Admin / Аdmin / adm1n)

function normAccount(key, a) {
  if (!a || typeof a !== 'object') return null;
  const nick = typeof a.nick === 'string' && a.nick ? a.nick : key;
  const r = { nick, created: +a.created || Date.now(), coins: Number.isFinite(+a.coins) ? Math.max(0, Math.floor(+a.coins)) : 500, owned: [], eq: {}, pets: Object.create(null), seen: [], adel: a.adel === true };
  if (a.ban && typeof a.ban === 'object') r.ban = { until: Math.max(0, +a.ban.until || 0), reason: clean(String(a.ban.reason || ''), 200), by: String(a.ban.by || '').slice(0, 16), at: +a.ban.at || 0 };
  if (a.pw && typeof a.pw === 'object' && typeof a.pw.h === 'string' && typeof a.pw.s === 'string') r.pw = { s: a.pw.s, h: a.pw.h, N: +a.pw.N || 16384, r: +a.pw.r || 8, p: +a.pw.p || 1 };
  else if (typeof a.hash === 'string') r.hash = a.hash;       // старый формат: SHA-256 из клиента, заменится на scrypt при первом входе
  else return null;                                            // без пароля аккаунт бесполезен
  const owned = Array.isArray(a.owned) ? a.owned : [];
  if (a.pets && typeof a.pets === 'object') for (const id of Object.keys(a.pets)) { const c = Math.floor(+a.pets[id]); if (EGG_IDS.has(id) && c > 0) r.pets[id] = Math.min(c, 1e9) }
  if (Array.isArray(a.seen)) r.seen = [...new Set(a.seen.filter(id => EGG_IDS.has(id)))];
  r.owned = [...new Set(owned.filter(k => SHOP_KEYS.has(k) || UKEY.test(k)))];
  const eq = a.eq && typeof a.eq === 'object' ? a.eq : {};
  for (const k of ['sh', 'hat', 'hair', 'acc', 'shirt', 'pants']) {
    const v = eq[k] === undefined ? null : eq[k];
    if (v === null) continue;
    if (typeof v === 'string' && UKEY.test(v)) { if (k !== 'sh') r.eq[k] = v; continue }   // существование вещи проверяется при показе (presEq)
    const it = (k === 'sh' || k === 'hat') ? shopItem(k, v) : null;
    if (it && (it[2] === 0 || r.owned.includes(shopKey(k, v)))) r.eq[k] = v;
  }

  if (a.lastLogin) r.lastLogin = +a.lastLogin || 0;
  if (typeof a.email === 'string' && a.email.length <= 120 && EMAIL_RE.test(a.email)) r.email = a.email.toLowerCase();   // только подтверждённая кодом
  const ids = v => Array.isArray(v) ? [...new Set(v.filter(x => typeof x === 'string' && x.length <= 16))].slice(0, 300) : [];
  r.fr = ids(a.fr); r.inc = ids(a.inc); r.out = ids(a.out);   // друзья, входящие и исходящие запросы (ключи аккаунтов)
  return r;
}

// ===== проверка содержимого плейса =====
const OBJ_TYPES = new Set(['cube', 'sphere', 'cyl', 'cone', 'plate', 'model', 'sound', 'bin', 'rig']);
const BIN_TYPES = new Set(['Script', 'GameTool', 'Grab', 'Clone', 'Hammer', 'Slingshot', 'Rocket', 'Laser']);
const num = (v, min, max, def) => { v = Number(v); return Number.isFinite(v) ? Math.min(max, Math.max(min, v)) : def };
const vec3 = (a, min, max, def) => Array.isArray(a) ? [0, 1, 2].map(i => num(a[i], min, max, def[i])) : def.slice();
const newObjId = () => 'o' + crypto.randomBytes(5).toString('hex');
function parseMaybe(v) { if (typeof v === 'string') { try { return JSON.parse(v) } catch { return null } } return v }

const RIG_J = ['head', 'torso', 'armL', 'armR', 'legL', 'legR'];
function cleanAnims(arr) {
  return (Array.isArray(arr) ? arr : []).slice(0, 20).map(a => {
    if (!a || typeof a !== 'object') return null;
    const kf = (Array.isArray(a.kf) ? a.kf : []).slice(0, 60).map(k => {
      if (!k || typeof k !== 'object') return null;
      const j = {}; const kj = k.j && typeof k.j === 'object' ? k.j : {};
      for (const n of RIG_J) if (Array.isArray(kj[n])) j[n] = vec3(kj[n], -360, 360, [0, 0, 0]);
      return { t: num(k.t, 0, 60, 0), j, y: num(k.y, -10, 10, 0) };
    }).filter(Boolean);
    return { n: clean(a.n, 30) || 'Anim', len: num(a.len, .1, 60, 1), loop: !!a.loop, kf };
  }).filter(Boolean);
}
function cleanObjs(v, strict) {
  const arr = parseMaybe(v);
  if (!Array.isArray(arr)) { if (strict) throw new Err('Некорректные данные плейса.'); return [] }
  if (arr.length > MAX_OBJS) { if (strict) throw new Err('Слишком много объектов (максимум ' + MAX_OBJS + ').'); arr.length = MAX_OBJS }
  const out = [], ids = new Set();
  for (const o of arr) {
    if (!o || typeof o !== 'object' || Array.isArray(o)) continue;
    const t = OBJ_TYPES.has(o.t) ? o.t : 'cube';
    let id = typeof o.id === 'string' && /^[A-Za-z0-9_-]{1,24}$/.test(o.id) && !ids.has(o.id) ? o.id : newObjId();
    ids.add(id);
    const c = {
      id, n: clean(o.n, 40) || 'Объект', t,
      p: vec3(o.p, -5000, 5000, [0, .5, 0]), r: vec3(o.r, -3600, 3600, [0, 0, 0]), s: vec3(o.s, .01, 1000, [1, 1, 1]),
      c: typeof o.c === 'string' && /^#[0-9a-fA-F]{6}$/.test(o.c) ? o.c.toLowerCase() : '#cccccc'
    };
    if (o.base === 1 || o.base === 2) c.base = o.base;
    if (t === 'model') { if (typeof o.src === 'string' && o.src.length <= MAX_SRC) c.src = o.src; else c.t = 'cube' }
    if (t === 'sound') {
      const q = o.snd && typeof o.snd === 'object' ? o.snd : {};
      const sn = { k: q.k === 'u' ? 'u' : 'p', id: typeof q.id === 'string' && /^[a-z0-9_]{1,20}$/.test(q.id) ? q.id : 'music1', vol: num(q.vol, 0, 1, .6), loop: !!q.loop, auto: !!q.auto, mus: !!q.mus, rad: num(q.rad, 0, 500, 0) };
      if (sn.k === 'u') { if (typeof q.src === 'string' && q.src.length <= MAX_AUDIO && AUDIO_RE.test(q.src)) sn.src = q.src; else sn.k = 'p' }
      c.snd = sn;
    }
    if (t === 'bin') { const q = o.bin && typeof o.bin === 'object' ? o.bin : {}; c.bin = { bt: BIN_TYPES.has(q.bt) ? q.bt : 'Script', ic: clean(q.ic, 8) || '🛠' } }
    if (t === 'rig') {
      const q = o.rig && typeof o.rig === 'object' ? o.rig : {};
      const anims = cleanAnims(q.anims);
      c.rig = { anims, play: clean(q.play, 30) || '', auto: !!q.auto };
    }
    out.push(c);
  }
  return out;
}
function cleanScripts(v, strict) {
  const arr = parseMaybe(v);
  if (!Array.isArray(arr)) { if (strict) throw new Err('Некорректные скрипты.'); return [] }
  if (arr.length > MAX_SCRIPTS) { if (strict) throw new Err('Слишком много скриптов (максимум ' + MAX_SCRIPTS + ').'); arr.length = MAX_SCRIPTS }
  const out = [];
  for (const s of arr) {
    if (!s || typeof s !== 'object' || Array.isArray(s) || typeof s.code !== 'string') continue;
    if (s.code.length > MAX_LUA) { if (strict) throw new Err('Скрипт слишком длинный (максимум ' + MAX_LUA + ' символов).'); continue }
    out.push({ n: clean(s.n, 60) || 'script', code: s.code });
  }
  return out;
}
function cleanContent(objs, scripts, strict) {
  const o = JSON.stringify(cleanObjs(objs, strict)), s = JSON.stringify(cleanScripts(scripts, strict));
  if (o.length + s.length > MAX_CONTENT) { if (strict) throw new Err('Плейс слишком большой — убери тяжёлые модели.'); return { objs: '[]', scripts: s.length < MAX_CONTENT ? s : '[]' } }
  return { objs: o, scripts: s };
}
function normPlace(id, p) {
  if (!p || typeof p !== 'object' || typeof p.owner !== 'string') return null;
  const r = { name: clean(p.name, 30) || 'Плейс', owner: p.owner, plays: Math.max(0, Math.floor(+p.plays || 0)), created: +p.created || +p.updated || Date.now(), updated: +p.updated || Date.now() };
  const c = cleanContent(p.objs, p.scripts, false); r.objs = c.objs; r.scripts = c.scripts;
  if (typeof p.desc === 'string') r.desc = clean(p.desc, 400);
  const ks = v => Array.isArray(v) ? [...new Set(v.filter(x => typeof x === 'string' && x.length <= 16))].slice(0, 10) : [];
  r.col = ks(p.col); r.inv = ks(p.inv); r.rev = Math.max(0, Math.floor(+p.rev || 0));   // соавторы, приглашения, версия сохранения
  if (typeof p.icon === 'string' && p.icon.length <= 120000 && ICON_RE.test(p.icon)) { r.icon = p.icon; r.iconV = +p.iconV || 1 }
  if (r.objs === '[]' && typeof p.blocks === 'string') { // старый блочный формат
    try { const b = JSON.parse(p.blocks); if (Array.isArray(b) && b.length <= 20000) r.blocks = JSON.stringify(b.filter(x => Array.isArray(x) && x.length >= 3).map(x => [num(x[0], -5000, 5000, 0), num(x[1], -5000, 5000, 0), num(x[2], -5000, 5000, 0), Math.floor(num(x[3], 0, 9, 0))])) } catch { }
  }
  return r;
}
(function normalizeAll() {
  const acc = nul();
  for (const k of Object.keys(DB.accounts)) {
    const a = normAccount(k, DB.accounts[k]); if (!a) continue;
    const key = k.toLowerCase(); if (acc[key]) continue;
    const sk = skeleton(a.nick); if (!SKEL.has(sk)) SKEL.set(sk, key);
    if (a.email) { if (EMAILS.has(a.email)) delete a.email; else EMAILS.set(a.email, key) }
    acc[key] = a;
  }
  DB.accounts = acc;
  const pl = nul(); for (const id of Object.keys(DB.places)) { const p = normPlace(id, DB.places[id]); if (p) pl[id] = p } DB.places = pl;
  const now = Date.now(), ss = nul();
  for (const h of Object.keys(DB.sessions)) { const s = DB.sessions[h]; if (s && typeof s.u === 'string' && DB.accounts[s.u] && s.exp > now) ss[h] = { u: s.u, exp: +s.exp, c: +s.c || now } }
  DB.sessions = ss;
})();

// --- запись: в SQLite пишутся только изменённые строки (одной транзакцией); в режиме JSON — файл целиком, атомарно ---
const dirtySet = new Set(); let saveTimer = null, writing = false, again = false, lastBak = 0;
const TABLE = { a: 'accounts', p: 'places', s: 'sessions', i: 'items', t: 'assets' }, COLL = { a: 'accounts', p: 'places', s: 'sessions', i: 'items', t: 'assets' };
function dirty(kind, key) { dirtySet.add(kind + ':' + key); save() }
function save() { if (!saveTimer) saveTimer = setTimeout(flush, sqlite ? 300 : 1000) }
function flushSqlite() {
  if (!dirtySet.size) return;
  const items = [...dirtySet]; dirtySet.clear();
  try {
    sqlite.exec('BEGIN');
    for (const it of items) {
      const kind = it[0], key = it.slice(2), t = TABLE[kind], rec = DB[COLL[kind]][key];
      if (rec === undefined) sqlite.prepare('DELETE FROM ' + t + ' WHERE k=?').run(key);
      else if (kind === 'p') sqlite.prepare('INSERT OR REPLACE INTO places(k,owner,data) VALUES(?,?,?)').run(key, rec.owner.toLowerCase(), JSON.stringify(rec));
      else sqlite.prepare('INSERT OR REPLACE INTO ' + t + '(k,data) VALUES(?,?)').run(key, JSON.stringify(rec));
    }
    sql
