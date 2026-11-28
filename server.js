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
  ['hat', null, 0], ['hat', 'cube', 150], ['hat', 'tall', 200], ['hat', 'crown', 500],
  ['shirt','blue',0],['shirt','red',50],['shirt','green',50],['shirt','purple',80],['shirt','black',80],
  ['pants','black',0],['pants','jeans',70],['pants','gray',50],['pants','olive',90],['pants','cargo',100],
  ['hair','brown',0],['hair','black',70],['hair','blond',80],['hair','spiky',100],['hair','long',120],
  ['hair','pack_01',0],['hair','pack_02',70],['hair','pack_03',90],['hair','pack_04',70],['hair','pack_05',90],['hair','pack_06',90],['hair','pack_07',100],['hair','pack_08',0],['hair','pack_09',110],['hair','pack_10',120],['hair','pack_11',120],['hair','pack_12',120],['hair','pack_13',130],['hair','pack_14',150]];
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
    const it = shopItem(k, v);
    if (it && (it[2] === 0 || r.owned.includes(shopKey(k, v)))) r.eq[k] = v;
  }
  // Existing and new accounts get the free starter outfit when a slot is empty.
  for (const [k, v] of [['shirt', 'blue'], ['pants', 'black'], ['hair', 'brown']]) {
    const it = shopItem(k, v);
    if (!Object.hasOwn(r.eq, k) && it && it[2] === 0) r.eq[k] = v;
  }

  if (typeof eq.hc === 'string' && /^#[0-9a-f]{6}$/i.test(eq.hc)) r.eq.hc = eq.hc.toLowerCase();
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
    sqlite.exec('COMMIT');
  } catch (e) { try { sqlite.exec('ROLLBACK') } catch { } for (const it of items) dirtySet.add(it); log('Ошибка записи в SQLite:', e.message); save() }
}
function flush() {
  saveTimer = null;
  if (sqlite) return flushSqlite();
  if (writing) { again = true; return }
  let json; try { json = JSON.stringify(DB) } catch (e) { log('Не удалось сериализовать базу:', e.message); return }
  writing = true; const tmp = FILE + '.tmp';
  const done = () => { writing = false; if (again) { again = false; save() } };
  const doWrite = () => fs.writeFile(tmp, json, { mode: 0o600 }, e => {
    if (e) { log('Ошибка записи data.json:', e.message); return done() }
    fs.rename(tmp, FILE, e2 => { if (e2) log('Ошибка переименования data.json:', e2.message); done() });
  });
  if (Date.now() - lastBak > 30 * 60e3 && fs.existsSync(FILE)) { lastBak = Date.now(); fs.copyFile(FILE, FILE + '.bak', doWrite) } else doWrite();
}
function flushSync() {
  clearTimeout(saveTimer); saveTimer = null;
  if (sqlite) { flushSqlite(); try { sqlite.close() } catch { } return }
  try { const tmp = FILE + '.tmp'; fs.writeFileSync(tmp, JSON.stringify(DB), { mode: 0o600 }); fs.renameSync(tmp, FILE) } catch (e) { log('Ошибка финальной записи:', e.message) }
}

// ===================== лимиты =====================
const buckets = new Map();   // токен-бакеты: key -> {v,t}
function take(key, rate, burst, cost = 1) {   // rate — токенов в секунду
  const now = Date.now(); let b = buckets.get(key);
  if (!b) { b = { v: burst, t: now }; buckets.set(key, b) }
  b.v = Math.min(burst, b.v + (now - b.t) / 1000 * rate); b.t = now;
  if (b.v < cost) return false; b.v -= cost; return true;
}
const fails = new Map();     // счётчики ошибок: key -> {n,until}
function failCount(key) { const f = fails.get(key); if (!f) return 0; if (f.reset < Date.now()) { fails.delete(key); return 0 } return f.n }
function failAdd(key, windowMs) { const f = fails.get(key); if (!f || f.reset < Date.now()) fails.set(key, { n: 1, reset: Date.now() + windowMs }); else f.n++ }
setInterval(() => {
  const now = Date.now();
  for (const [k, b] of buckets) if (now - b.t > 10 * 60e3) buckets.delete(k);
  for (const [k, f] of fails) if (f.reset < now) fails.delete(k);
  for (const h of Object.keys(DB.sessions)) if (DB.sessions[h].exp < now) { delete DB.sessions[h]; dirty('s', h) }
  for (const [k, t] of playSeen) if (now - t > 36e5) playSeen.delete(k);
}, 60e3).unref();

// ===================== IP / HTTPS =====================
const isPrivateIp = ip => /^(127\.|10\.|192\.168\.|172\.(1[6-9]|2\d|3[01])\.|::1$|f[cd][0-9a-f]{2}:|fe80:)/i.test(ip);
const normIp = ip => String(ip || '').replace(/^::ffff:/i, '');
function clientIp(req) {
  const peer = normIp(req.socket.remoteAddress);
  const hops = TRUST_HOPS == null ? (isPrivateIp(peer) ? 1 : 0) : TRUST_HOPS;
  if (hops > 0) {
    const xf = String(req.headers['x-forwarded-for'] || '').split(',').map(s => normIp(s.trim())).filter(Boolean);
    if (xf.length) { const ip = xf[Math.max(0, xf.length - hops)]; if (net.isIP(ip)) return ip }
  }
  return peer || 'unknown';
}
function isSecure(req) {
  if (req.socket.encrypted) return true;
  const peer = normIp(req.socket.remoteAddress), hops = TRUST_HOPS == null ? (isPrivateIp(peer) ? 1 : 0) : TRUST_HOPS;
  return hops > 0 && String(req.headers['x-forwarded-proto'] || '').split(',')[0].trim() === 'https';
}

// ===================== пароли и сессии =====================
const SCRYPT = { N: 16384, r: 8, p: 1 };
const scrypt = (pw, salt, o) => new Promise((res, rej) => crypto.scrypt(pw, salt, 64, { N: o.N, r: o.r, p: o.p, maxmem: 128 * o.N * o.r * 2 }, (e, k) => e ? rej(e) : res(k)));
let hashing = 0;
async function guarded(fn) {   // не даём забить сервер одновременными scrypt
  if (hashing >= 12) throw new Err('Сервер перегружен, повтори через несколько секунд.');
  hashing++; try { return await fn() } finally { hashing-- }
}
const normPw = p => p.normalize('NFKC');
const hashPw = pw => guarded(async () => { const salt = crypto.randomBytes(16); const h = await scrypt(normPw(pw), salt, SCRYPT); return { s: salt.toString('hex'), h: h.toString('hex'), ...SCRYPT } });
const checkPw = (pw, rec) => guarded(async () => {
  const want = Buffer.from(rec.h, 'hex'); const got = await scrypt(normPw(pw), Buffer.from(rec.s, 'hex'), rec);
  return want.length === got.length && crypto.timingSafeEqual(want, got);
});
let DUMMY = null;   // чтобы вход под несуществующим ником занимал столько же времени
hashPw('dummy-password').then(d => DUMMY = d).catch(() => { });
const legacyHash = (key, pw) => sha(key + ':' + pw + ':bv');
const safeEq = (a, b) => { const x = Buffer.from(String(a)), y = Buffer.from(String(b)); return x.length === y.length && crypto.timingSafeEqual(x, y) };

function newSession(key) {
  const token = crypto.randomBytes(32).toString('base64url'), now = Date.now();
  DB.sessions[sha(token)] = { u: key, exp: now + SESSION_MS, c: now };
  const mine = Object.keys(DB.sessions).filter(h => DB.sessions[h].u === key).sort((a, b) => DB.sessions[a].c - DB.sessions[b].c);
  while (mine.length > MAX_SESSIONS_PER_USER) { const old = mine.shift(); delete DB.sessions[old]; dirty('s', old) }
  dirty('s', sha(token)); return token;
}
function sessionByToken(token) {
  if (typeof token !== 'string' || token.length < 20 || token.length > 100) return null;
  const h = sha(token), s = DB.sessions[h]; if (!s) return null;
  if (s.exp < Date.now() || !DB.accounts[s.u]) { delete DB.sessions[h]; dirty('s', h); return null }
  return { h, key: s.u };
}
const maskEmail = e => { const [u, d] = String(e).split('@'); return u.slice(0, 1) + '***@' + d };
const ADMINS = new Set(['абоба']);   // ники администраторов (в нижнем регистре)
const banActive = a => !!(a && a.ban && (a.ban.until === 0 || a.ban.until > Date.now()));
const banMsg = a => 'Аккаунт заблокирован ' + (a.ban.until ? 'до ' + new Date(a.ban.until).toLocaleString('ru-RU') : 'навсегда') + '. Причина: ' + (a.ban.reason || 'не указана');
const pub = a => ({ admin: ADMINS.has(String(a.nick).toLowerCase()), nick: a.nick, coins: a.coins, owned: a.owned.slice(), eq: { ...a.eq }, pets: { ...a.pets }, seen: (a.seen || []).slice(), adel: !!a.adel, email: a.email ? maskEmail(a.email) : null });

// ===================== HTTP =====================
// ---- обновления: версия считается САМА по датам файлов игры (server.js и public/). Ничего менять вручную не нужно.
// Необязательно: в update.json можно написать "notes" — этот текст увидят игроки в окне обновления.
let verCache = null, verAt = 0;
function versionInfo() {
  if (verCache && Date.now() - verAt < 5000) return verCache;
  const mt = f => { try { return Math.floor(fs.statSync(f).mtimeMs) } catch { return 0 } };
  let t = mt(__filename), notes = '';
  try { for (const n of fs.readdirSync(PUB)) t = Math.max(t, mt(path.join(PUB, n))) } catch { }
  try { const up = JSON.parse(fs.readFileSync(path.join(__dirname, 'update.json'), 'utf8')); if (typeof up.notes === 'string') notes = up.notes.slice(0, 600) } catch { }
  verAt = Date.now();
  let name = ''; try { name = JSON.parse(fs.readFileSync(path.join(__dirname, 'package.json'), 'utf8')).version } catch { }
  return verCache = { version: t.toString(36), name, notes };
}
const MIME = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8', '.json': 'application/json; charset=utf-8', '.png': 'image/png', '.jpg': 'image/jpeg', '.svg': 'image/svg+xml', '.ico': 'image/x-icon', '.txt': 'text/plain; charset=utf-8', '.woff2': 'font/woff2', '.webmanifest': 'application/manifest+json; charset=utf-8' };
const SEC_HEADERS = { 'X-Content-Type-Options': 'nosniff', 'X-Frame-Options': 'DENY', 'Referrer-Policy': 'no-referrer',
  'Content-Security-Policy': "frame-ancestors 'none'; object-src 'none'; base-uri 'none'; form-action 'none'", 'Permissions-Policy': 'camera=(), microphone=(), geolocation=()' };
const srv = http.createServer((q, r) => {
  try {
    if (q.method !== 'GET' && q.method !== 'HEAD') { r.writeHead(405, { Allow: 'GET, HEAD', ...SEC_HEADERS }); return r.end() }
    if (REQUIRE_HTTPS && !isSecure(q) && q.url !== '/healthz') { const h = String(q.headers.host || '').replace(/[^\w.:\-\[\]]/g, ''); r.writeHead(301, { Location: 'https://' + h + q.url.replace(/[\r\n]/g, ''), ...SEC_HEADERS }); return r.end() }
    if (isSecure(q)) SEC_HEADERS['Strict-Transport-Security'] = 'max-age=15552000';
    let u; try { u = decodeURIComponent(String(q.url).split('?')[0].split('#')[0]) } catch { r.writeHead(400, SEC_HEADERS); return r.end('Bad request') }
    if (u.includes('\0')) { r.writeHead(400, SEC_HEADERS); return r.end('Bad request') }
    if (u === '/healthz') { r.writeHead(200, { 'Content-Type': 'text/plain', 'Cache-Control': 'no-store', ...SEC_HEADERS }); return r.end('ok') }
    if (u === '/version.json') { r.writeHead(200, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store', 'Access-Control-Allow-Origin': '*', ...SEC_HEADERS }); return r.end(JSON.stringify(versionInfo())) }
    if (u.startsWith('/icon/')) {
      const id = u.slice(6), pl = Object.hasOwn(DB.places, id) ? DB.places[id] : null, mm = pl && pl.icon ? ICON_RE.exec(pl.icon) : null;
      if (!mm) { r.writeHead(404, SEC_HEADERS); return r.end() }
      r.writeHead(200, { 'Content-Type': 'image/' + mm[1], 'Cache-Control': 'public, max-age=86400', ...SEC_HEADERS });
      return r.end(q.method === 'HEAD' ? undefined : Buffer.from(mm[2], 'base64'));
    }
    if (u.startsWith('/itex/')) {
      const id = u.slice(6), it = Object.hasOwn(DB.items, id) ? DB.items[id] : null, mm = it && it.tex ? TEX_RE.exec(it.tex) : null;
      if (!mm) { r.writeHead(404, SEC_HEADERS); return r.end() }
      r.writeHead(200, { 'Content-Type': 'image/' + mm[1], 'Cache-Control': 'public, max-age=86400', ...SEC_HEADERS });
      return r.end(q.method === 'HEAD' ? undefined : Buffer.from(mm[2], 'base64'));
    }
    if (u === '/') u = '/index.html';
    const p = path.resolve(PUB, '.' + u);
    if (p !== PUB && !p.startsWith(PUB + path.sep)) { r.writeHead(403, SEC_HEADERS); return r.end('403') }
    fs.readFile(p, (e, d) => {
      if (e) { r.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8', ...SEC_HEADERS }); return r.end('404') }
      const ext = path.extname(p).toLowerCase();
      r.writeHead(200, { 'Content-Type': MIME[ext] || 'application/octet-stream', 'Cache-Control': ext === '.html' || ext === '.js' ? 'no-cache' : 'public, max-age=3600', ...SEC_HEADERS });
      r.end(q.method === 'HEAD' ? undefined : ext === '.html' ? d.toString('utf8').replace(/__V__/g, versionInfo().version) : d);
    });
  } catch (e) { log('HTTP ошибка:', e.message); try { r.writeHead(500); r.end() } catch { } }
});
srv.headersTimeout = 20000; srv.requestTimeout = 30000; srv.keepAliveTimeout = 10000;

// ===================== WebSocket =====================
const wss = new WebSocketServer({ noServer: true, maxPayload: 3 * 1024 * 1024, perMessageDeflate: false });
const rooms = new Map();            // ключ сервера 'плейс|инстанс' -> Set<ws>
const RMETA = new Map(), PLACE_ROOMS = new Map(), CODES = new Map();   // метаданные серверов, серверы по плейсу, коды частных серверов
const CODE_ABC = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
const dirtyRooms = new Set();
const ipConns = new Map();
const playSeen = new Map();
let nPid = 0, totalConn = 0;

function originOk(req) {
  const o = req.headers.origin; if (!o || o === 'null' || o.startsWith('file:')) return true;   // приложение Android (file://); токены не в cookie — CSWSH невозможен           // не браузер — CSWSH невозможен
  let host; try { host = new URL(o).host.toLowerCase() } catch { return false }
  if (ALLOWED_ORIGINS.includes(o.toLowerCase()) || ALLOWED_ORIGINS.includes(host)) return true;
  return host === String(req.headers.host || '').toLowerCase();
}
srv.on('upgrade', (req, sock, head) => {
  sock.on('error', () => { });
  const deny = (c, t) => { try { sock.write('HTTP/1.1 ' + c + ' ' + t + '\r\nConnection: close\r\n\r\n') } catch { } sock.destroy() };
  try {
    if (!originOk(req)) return deny(403, 'Forbidden');
    const ip = clientIp(req);
    if (totalConn >= MAX_CONN || (ipConns.get(ip) || 0) >= MAX_CONN_IP) return deny(429, 'Too Many Requests');
    if (!take('conn:' + ip, 2, 20)) return deny(429, 'Too Many Requests');
    wss.handleUpgrade(req, sock, head, ws => { ws.ip = ip; wss.emit('connection', ws, req) });
  } catch (e) { log('upgrade ошибка:', e.message); deny(400, 'Bad Request') }
});

const send = (w, o) => { if (w.readyState === 1) { if (w.bufferedAmount > 4e6) { w.terminate(); return } w.send(typeof o === 'string' ? o : JSON.stringify(o)) } };

// --- список плейсов для главной (лёгкие метаданные, без содержимого) ---
let metaCache = null, snapTimer = null;
const metaOf = p => ({ name: p.name, owner: p.owner, plays: p.plays, updated: p.updated, ic: p.icon ? p.iconV || 1 : 0, col: p.col && p.col.length ? p.col : undefined });
function metaList() {
  if (!metaCache) {
    const all = Object.keys(DB.places).map(id => [id, DB.places[id]]);
    all.sort((a, b) => b[1].plays - a[1].plays || b[1].updated - a[1].updated);
    metaCache = all;
  }
  return metaCache;
}
function snapFor(ws) {
  const all = metaList(), docs = nul(); const top = all.slice(0, 1000);
  for (const [id, p] of top) docs[id] = metaOf(p);
  if (all.length > 1000 && ws.u) for (const [id, p] of all.slice(1000)) if (p.owner.toLowerCase() === ws.u) docs[id] = metaOf(p);
  return { t: 'snap', c: 'places', docs };
}
function placesChanged() {
  metaCache = null; if (snapTimer) return;
  snapTimer = setTimeout(() => { snapTimer = null; for (const w of wss.clients) if (w.subs && w.u) send(w, snapFor(w)) }, 1500);
}

// --- комнаты ---
function roomPeers(id) {
  const S = rooms.get(id); if (!S) return [];
  return [...S].filter(w => w.pres).map(w => ({ peer: w.pid, presence: w.pres }));
}
setInterval(() => {   // не чаще 10 раз в секунду на комнату
  for (const id of dirtyRooms) { const S = rooms.get(id); if (!S) continue; const msg = JSON.stringify({ t: 'peers', peers: roomPeers(id) }); for (const w of S) send(w, msg) }
  dirtyRooms.clear();
}, 100).unref();
function dropRoom(key) {
  rooms.delete(key); dirtyRooms.delete(key);
  const mt = RMETA.get(key); RMETA.delete(key); if (!mt) return;
  const set = PLACE_ROOMS.get(mt.place); if (set) { set.delete(key); if (!set.size) PLACE_ROOMS.delete(mt.place) }
  if (mt.code) CODES.delete(mt.code);
}
function leaveRoom(w) {
  const id = w.room; if (!id) return; w.room = null; w.pres = null;
  const S = rooms.get(id); if (!S) return; S.delete(w);
  if (S.size) dirtyRooms.add(id); else dropRoom(id);
}
function mkRoom(place, priv) {
  let inst, key; do { inst = crypto.randomBytes(3).toString('hex'); key = place + '|' + inst } while (rooms.has(key));
  let code = null; if (priv) do { code = Array.from({ length: 6 }, () => CODE_ABC[crypto.randomInt(CODE_ABC.length)]).join('') } while (CODES.has(code));
  rooms.set(key, new Set()); RMETA.set(key, { place, inst, priv: !!priv, code });
  let set = PLACE_ROOMS.get(place); if (!set) PLACE_ROOMS.set(place, set = new Set()); set.add(key);
  if (code) CODES.set(code, key);
  return key;
}

// --- вспомогательное ---
function need(ws) {   // требует вход; проверяет, что сессия ещё жива
  if (!ws.u) throw new Err('Нужно войти в аккаунт.', 'auth');
  const s = DB.sessions[ws.sh], now = Date.now();
  if (!s || s.exp < now || !DB.accounts[ws.u]) { dropAuth(ws); throw new Err('Сессия истекла, войди снова.', 'auth') }
  if (banActive(DB.accounts[ws.u]) && !ADMINS.has(ws.u)) { const bm = banMsg(DB.accounts[ws.u]); dropAuth(ws); throw new Err(bm, 'auth') }
  if (s.exp - now < SESSION_MS - 864e5) { s.exp = now + SESSION_MS; dirty('s', ws.sh) }
  return DB.accounts[ws.u];
}
function dropAuth(ws) { leaveRoom(ws); ws.subs = false; ws.u = null; ws.sh = null }
function setAuth(ws, key, sh) { if (ws.u !== key) { leaveRoom(ws); ws.subs = false } ws.u = key; ws.sh = sh }
function secureAuthOnly(ws) { if (REQUIRE_HTTPS && !ws.secure) throw new Err('Вход возможен только по HTTPS.') }
function validNick(n) {
  if (typeof n !== 'string' || !/^[A-Za-z0-9_А-яЁё]{3,16}$/.test(n)) return 'Ник: 3–16 символов (буквы, цифры, _).';
  if (/[A-Za-z]/.test(n) && /[Ѐ-ӿ]/.test(n)) return 'Ник не может смешивать русские и английские буквы.';
  return null;
}
const COMMON_PW = new Set(['123456', '1234567', '12345678', '123456789', '1234567890', 'password', 'password1', 'qwerty', 'qwerty123', '111111', '123123', 'qwertyuiop', 'йцукен', 'abc123', '000000', '12345678910', 'iloveyou', 'blockverse', 'voxelblox', 'voxelblox']);
function validPw(p, nick) {
  if (typeof p !== 'string' || p.length < 6) return 'Пароль: минимум 6 символов.';
  if (p.length > 128) return 'Пароль слишком длинный (максимум 128).';
  if (COMMON_PW.has(p.toLowerCase()) || p.toLowerCase() === nick.toLowerCase()) return 'Слишком простой пароль, придумай другой.';
  return null;
}
const rateUser = (ws, name, rate, burst) => { if (!take(name + ':' + ws.u, rate, burst)) throw new Err('Слишком часто, подожди секунду.') };
const strId = v => typeof v === 'string' && v.length > 0 && v.length <= 40 ? v : null;

// ===================== обработчики =====================
const H = nul();

H.register = async (ws, m) => {
  secureAuthOnly(ws);
  if (!take('regtry:' + ws.ip, 0.05, 40)) throw new Err('Слишком много попыток. Подожди немного.');
  const nick = typeof m.nick === 'string' ? m.nick.trim() : '', pass = m.pass;
  const e1 = validNick(nick); if (e1) throw new Err(e1);
  const e2 = validPw(pass, nick); if (e2) throw new Err(e2);
  const key = nick.toLowerCase(), sk = skeleton(nick);
  if (DB.accounts[key] || SKEL.has(sk) || RESERVED.has(sk)) throw new Err('Этот ник уже занят.');
  if (!take('reg:' + ws.ip, 10 / 3600, 10)) throw new Err('Слишком много регистраций с этого адреса. Попробуй позже.');
  const pw = await hashPw(pass);
  if (DB.accounts[key] || SKEL.has(sk)) throw new Err('Этот ник уже занят.');   // повторная проверка: за время хэширования мог зарегистрироваться другой
  const a = { nick, pw, created: Date.now(), coins: 500, owned: [], eq: {}, pets: nul(), seen: [], adel: false, lastLogin: Date.now(), fr: [], inc: [], out: [] };
  DB.accounts[key] = a; SKEL.set(sk, key);
  const token = newSession(key); setAuth(ws, key, sha(token)); dirty('a', key);
  return { token, me: pub(a) };
};

H.login = async (ws, m) => {
  secureAuthOnly(ws);
  const nick = typeof m.nick === 'string' ? m.nick.trim().slice(0, 40) : '', pass = typeof m.pass === 'string' ? m.pass : '';
  const key = nick.toLowerCase(), kIp = 'f:ip:' + ws.ip, kIpNick = 'f:in:' + ws.ip + ':' + key, kNick = 'f:n:' + key;
  if (failCount(kIp) >= 25 || failCount(kIpNick) >= 6 || failCount(kNick) >= 60) throw new Err('Слишком много неудачных попыток. Подожди 15 минут.');
  if (!nick || !pass || pass.length > 128) { failAdd(kIp, 9e5); throw new Err('Неверный ник или пароль.') }
  const a = Object.hasOwn(DB.accounts, key) ? DB.accounts[key] : null;
  let ok = false;
  if (!a) { if (DUMMY) await checkPw(pass, DUMMY).catch(() => { }) }
  else if (a.pw) ok = await checkPw(pass, a.pw);
  else if (a.hash) {   // миграция со старого формата
    ok = safeEq(legacyHash(key, pass), a.hash);
    if (ok) { const pw = await hashPw(pass); if (DB.accounts[key] === a) { a.pw = pw; delete a.hash; dirty('a', key) } }
  }
  if (!ok || DB.accounts[key] !== a) { failAdd(kIp, 9e5); failAdd(kIpNick, 9e5); failAdd(kNick, 36e5); throw new Err('Неверный ник или пароль.') }
  fails.delete(kIpNick);
  if (banActive(a) && !ADMINS.has(key)) throw new Err(banMsg(a));
  a.lastLogin = Date.now();
  const token = newSession(key); setAuth(ws, key, sha(token)); dirty('a', key);
  return { token, me: pub(a) };
};

H.resume = async (ws, m) => {
  if (!take('res:' + ws.ip, 1, 30)) throw new Err('Слишком часто.');
  const s = sessionByToken(m.token);
  if (!s) throw new Err('Сессия истекла, войди снова.', 'auth');
  if (banActive(DB.accounts[s.key]) && !ADMINS.has(s.key)) throw new Err(banMsg(DB.accounts[s.key]), 'auth');
  setAuth(ws, s.key, s.h);
  return { me: pub(DB.accounts[s.key]) };
};

H.logout = async ws => { if (ws.sh) { const h = ws.sh; delete DB.sessions[h]; dirty('s', h) } dropAuth(ws); return 1 };

H.me = async ws => pub(need(ws));

// ===================== почта: привязка e-mail и восстановление пароля =====================
// Почта считается привязанной ТОЛЬКО после ввода 6-значного кода, присланного на неё: так никто не может привязать чужой адрес.
// Сбросить пароль можно только через подтверждённую почту аккаунта; код живёт 10 минут, 5 попыток, одноразовый.
const SMTP = { host: process.env.SMTP_HOST || '', port: +process.env.SMTP_PORT || 465, user: process.env.SMTP_USER || '', pass: process.env.SMTP_PASS || '' };
SMTP.from = process.env.SMTP_FROM || SMTP.user || 'no-reply@voxelblox.local';
SMTP.secure = process.env.SMTP_SECURE != null ? process.env.SMTP_SECURE === '1' : SMTP.port === 465;
const b64 = s => Buffer.from(s, 'utf8').toString('base64');
const addrOnly = s => (/<([^>]+)>/.exec(s) || [null, s])[1].trim();
function smtpSend(to, subject, text) {
  return new Promise((resolve, reject) => {
    let sock, buf = '', waiter = null, done = false;
    const fail = e => { if (done) return; done = true; try { sock && sock.destroy() } catch { } reject(e instanceof Error ? e : new Error(String(e))) };
    const timer = setTimeout(() => fail(new Error('SMTP: таймаут')), 25000);
    const feed = d => {
      buf += d.toString('utf8');
      for (;;) {   // ответ закончен строкой вида "250 text" (после кода — пробел)
        const lines = buf.split('\r\n'); if (lines.length < 2) return;
        const idx = lines.findIndex((l, i) => i < lines.length - 1 && /^\d{3} /.test(l)); if (idx < 0) return;
        const resp = lines.slice(0, idx + 1); buf = lines.slice(idx + 1).join('\r\n');
        const w = waiter; waiter = null; if (w) w({ code: +resp[idx].slice(0, 3), text: resp.join('\n') });
      }
    };
    const wait = () => new Promise(r => { waiter = r });
    const cmd = async (line, ok) => { sock.write(line + '\r\n'); const r = await wait(); if (!ok.includes(r.code)) throw new Error('SMTP ' + r.code + ' на «' + line.split(' ')[0] + '»'); return r };
    const attach = s => { sock = s; s.on('data', feed); s.on('error', fail); s.on('close', () => { if (!done) fail(new Error('SMTP: соединение закрыто')) }) };
    (async () => {
      const opts = { host: SMTP.host, port: SMTP.port, servername: SMTP.host };
      await new Promise((res, rej) => { const s = SMTP.secure ? tls.connect(opts, res) : net.connect(SMTP.port, SMTP.host, res); s.once('error', rej); attach(s) });
      let r = await wait(); if (r.code !== 220) throw new Error('SMTP: сервер не готов');
      const ehlo = await cmd('EHLO voxelblox', [250]);
      if (!SMTP.secure && /STARTTLS/i.test(ehlo.text)) {
        await cmd('STARTTLS', [220]);
        sock.removeAllListeners('data'); sock.removeAllListeners('close'); sock.removeAllListeners('error');
        await new Promise((res, rej) => { const s = tls.connect({ socket: sock, servername: SMTP.host }, res); s.once('error', rej); attach(s) });
        await cmd('EHLO voxelblox', [250]);
      }
      if (SMTP.user) { await cmd('AUTH LOGIN', [334]); await cmd(b64(SMTP.user), [334]); await cmd(b64(SMTP.pass), [235]) }
      await cmd('MAIL FROM:<' + addrOnly(SMTP.from) + '>', [250]);
      await cmd('RCPT TO:<' + to + '>', [250, 251]);
      await cmd('DATA', [354]);
      const body = b64(text).replace(/(.{76})/g, '$1\r\n');
      const msg = ['From: ' + SMTP.from.replace(/[\r\n]/g, ''), 'To: <' + to + '>', 'Subject: =?UTF-8?B?' + b64(subject) + '?=', 'Date: ' + new Date().toUTCString(),
        'Message-ID: <' + crypto.randomBytes(12).toString('hex') + '@voxelblox>', 'MIME-Version: 1.0', 'Content-Type: text/plain; charset=utf-8', 'Content-Transfer-Encoding: base64', '', body].join('\r\n');
      await cmd(msg + '\r\n.', [250]);
      try { sock.write('QUIT\r\n') } catch { }
      done = true; clearTimeout(timer); try { sock.end() } catch { } resolve(true);
    })().catch(e => { clearTimeout(timer); fail(e) });
  });
}
async function sendMail(to, subject, text) {
  if (!SMTP.host) { log('[ПОЧТА не настроена — SMTP_HOST не задан] кому:', to, '|', subject, '\n' + text); return false }
  await smtpSend(to, subject, text); return true;
}
const MAIL_TX = {
  verify: { en: ['VoxelBlox: confirm your email', c => 'Your VoxelBlox confirmation code: ' + c + '\n\nEnter it in Settings → Account to link this email to your account.\nThe code works for 10 minutes. If you did not request it, just ignore this email.'],
    ru: ['VoxelBlox: подтверждение почты', c => 'Ваш код подтверждения VoxelBlox: ' + c + '\n\nВведите его в Настройки → Аккаунт, чтобы привязать эту почту к аккаунту.\nКод действует 10 минут. Если вы его не запрашивали — просто проигнорируйте письмо.'] },
  reset: { en: ['VoxelBlox: password reset code', (c, n) => 'Someone asked to reset the password for the account "' + n + '".\n\nYour code: ' + c + '\n\nIt works for 10 minutes. If this was not you, ignore this email: your password stays the same.'],
    ru: ['VoxelBlox: код для сброса пароля', (c, n) => 'Кто-то запросил сброс пароля для аккаунта «' + n + '».\n\nВаш код: ' + c + '\n\nОн действует 10 минут. Если это были не вы — проигнорируйте письмо, пароль останется прежним.'] },
};
const MAILV = new Map();   // коды: 'v:ключ' (привязка) / 'r:ключ' (сброс) -> {salt,h,email,exp,tries}
setInterval(() => { const n = Date.now(); for (const [k, v] of MAILV) if (v.exp < n) MAILV.delete(k) }, 60e3).unref();
function issueCode(slot, email) {
  const code = String(crypto.randomInt(1000000)).padStart(6, '0'), salt = crypto.randomBytes(8).toString('hex');
  MAILV.set(slot, { salt, h: sha(salt + code), email, exp: Date.now() + 10 * 60e3, tries: 0 });
  return code;
}
function checkCode(slot, code) {   // true / false; после 5 неверных попыток код сгорает
  const r = MAILV.get(slot); if (!r || r.exp < Date.now()) { MAILV.delete(slot); return null }
  if (typeof code !== 'string' || !/^\d{6}$/.test(code.trim())) { if (++r.tries >= 5) MAILV.delete(slot); return false }
  if (++r.tries > 5) { MAILV.delete(slot); return false }
  if (safeEq(sha(r.salt + code.trim()), r.h)) { MAILV.delete(slot); return r }
  if (r.tries >= 5) MAILV.delete(slot);
  return false;
}
const normEmail = e => typeof e === 'string' ? e.trim().toLowerCase() : '';
const langOf = m => m && m.lang === 'ru' ? 'ru' : 'en';
async function needPw(ws, a, pass) {   // повторный ввод пароля для опасных действий
  if (typeof pass !== 'string' || !pass || pass.length > 128 || !a.pw) throw new Err('Введи свой пароль.');
  const k = 'f:pw:' + ws.u; if (failCount(k) >= 8) throw new Err('Слишком много неудачных попыток. Подожди 15 минут.');
  if (!(await checkPw(pass, a.pw))) { failAdd(k, 9e5); throw new Err('Неверный пароль.') }
}

H['email.set'] = async (ws, m) => {   // шаг 1: отправить код на новую почту
  secureAuthOnly(ws); const a = need(ws); const email = normEmail(m.email);
  if (email.length > 120 || !EMAIL_RE.test(email)) throw new Err('Введи правильный адрес почты.');
  await needPw(ws, a, m.pass);
  if (a.email === email) throw new Err('Эта почта уже привязана к твоему аккаунту.');
  if (EMAILS.has(email)) throw new Err('Эта почта уже привязана к другому аккаунту.');
  if (!take('emset:' + ws.u, 1 / 60, 1)) throw new Err('Подожди минуту перед следующим письмом.');
  if (!take('emto:' + email, 5 / 3600, 5) || !take('emip:' + ws.ip, 20 / 3600, 20)) throw new Err('Слишком много писем. Попробуй позже.');
  const code = issueCode('v:' + ws.u, email), tx = MAIL_TX.verify[langOf(m)];
  try { await sendMail(email, tx[0], tx[1](code)) } catch (e) { MAILV.delete('v:' + ws.u); log('Не удалось отправить письмо:', e.message); throw new Err('Не удалось отправить письмо. Проверь адрес или попробуй позже.') }
  return { sent: true };
};
H['email.verify'] = async (ws, m) => {   // шаг 2: ввести код — почта привязана
  secureAuthOnly(ws); const a = need(ws);
  const r = checkCode('v:' + ws.u, m.code);
  if (r === null) throw new Err('Код устарел. Запроси новый.');
  if (r === false) throw new Err('Неверный код.');
  if (EMAILS.has(r.email) && EMAILS.get(r.email) !== ws.u) throw new Err('Эта почта уже привязана к другому аккаунту.');
  if (a.email) EMAILS.delete(a.email);
  a.email = r.email; EMAILS.set(r.email, ws.u); dirty('a', ws.u);
  return { me: pub(a) };
};
H['email.remove'] = async (ws, m) => {
  secureAuthOnly(ws); const a = need(ws); await needPw(ws, a, m.pass);
  if (a.email) { EMAILS.delete(a.email); delete a.email; dirty('a', ws.u) }
  MAILV.delete('v:' + ws.u);
  return { me: pub(a) };
};
H['pw.forgot'] = async (ws, m) => {   // не пользователь «вошёл», а владелец почты: ответ всегда одинаковый, чтобы нельзя было выяснять, кто зарегистрирован
  secureAuthOnly(ws);
  if (!take('fg:' + ws.ip, 10 / 3600, 10)) throw new Err('Слишком много попыток. Подожди немного.');
  const nick = typeof m.nick === 'string' ? m.nick.trim().slice(0, 40) : '', email = normEmail(m.email), key = nick.toLowerCase();
  if (!nick || email.length > 120 || !EMAIL_RE.test(email)) throw new Err('Введи ник и адрес почты.');
  const a = Object.hasOwn(DB.accounts, key) ? DB.accounts[key] : null;
  if (a && a.email && a.email === email && take('fgk:' + key, 5 / 3600, 5)) {
    const code = issueCode('r:' + key, email), tx = MAIL_TX.reset[langOf(m)];
    sendMail(email, tx[0], tx[1](code, a.nick)).catch(e => log('Не удалось отправить письмо:', e.message));
  }
  return { sent: true };
};
H['pw.reset'] = async (ws, m) => {
  secureAuthOnly(ws);
  const nick = typeof m.nick === 'string' ? m.nick.trim().slice(0, 40) : '', key = nick.toLowerCase(), kIp = 'f:rip:' + ws.ip, kN = 'f:rn:' + key;
  if (failCount(kIp) >= 20 || failCount(kN) >= 10) throw new Err('Слишком много неудачных попыток. Подожди 15 минут.');
  const a = Object.hasOwn(DB.accounts, key) ? DB.accounts[key] : null;
  const r = a ? checkCode('r:' + key, m.code) : false;
  if (!r) { failAdd(kIp, 9e5); failAdd(kN, 9e5); throw new Err('Неверный или просроченный код.') }
  if (a.email !== r.email) throw new Err('Неверный или просроченный код.');
  const e2 = validPw(m.pass, a.nick); if (e2) { MAILV.set('r:' + key, r); r.tries = Math.max(0, r.tries - 1); throw new Err(e2) }
  const pw = await hashPw(m.pass);
  a.pw = pw; delete a.hash; dirty('a', key);
  for (const h of Object.keys(DB.sessions)) if (DB.sessions[h].u === key) { delete DB.sessions[h]; dirty('s', h) }   // все старые входы разлогиниваются
  for (const w of wss.clients) if (w.u === key) dropAuth(w);
  fails.delete(kN);
  return { ok: true };
};


// ===================== вещи, созданные игроками =====================
const ISLOTS = new Set(['hair', 'hat', 'acc', 'shirt', 'pants']), MAX_ITEMS_PER_USER = 30, MAX_PRICE = 500, MAX_PARTS = 24, MAX_TEX = 90000;
const TEX_RE = /^data:image\/(png|jpeg);base64,([A-Za-z0-9+\/]+={0,2})$/;
function cleanParts(v) {
  if (!Array.isArray(v)) return null; const out = [];
  for (const p of v.slice(0, MAX_PARTS)) {
    if (!Array.isArray(p) || p.length < 7 || typeof p[6] !== 'string' || !/^#[0-9a-fA-F]{6}$/.test(p[6])) continue;
    out.push([num(p[0], -3, 3, 0), num(p[1], -4, 3.5, 0), num(p[2], -3, 3, 0), num(p[3], .05, 2.6, .5), num(p[4], .05, 2.6, .5), num(p[5], .05, 2.6, .5), p[6].toLowerCase()].map(x => typeof x === 'number' ? +x.toFixed(3) : x));
  }
  return out.length ? out : null;
}
function normItem(id, it) {
  if (!it || typeof it !== 'object' || !ISLOTS.has(it.slot) || typeof it.owner !== 'string') return null;
  const r = { name: clean(it.name, 30) || 'Вещь', slot: it.slot, owner: it.owner, price: Math.floor(num(it.price, 0, MAX_PRICE, 0)), created: +it.created || Date.now(), sales: Math.max(0, Math.floor(+it.sales || 0)), rep: Array.isArray(it.rep) ? it.rep.filter(x => typeof x === 'string').slice(0, 10) : [] };
  if (it.slot === 'shirt' || it.slot === 'pants') { if (typeof it.tex === 'string' && it.tex.length <= MAX_TEX && TEX_RE.test(it.tex)) r.tex = it.tex; else return null }
  else { const p = cleanParts(it.parts); if (!p) return null; r.parts = p }
  return r;
}
const itemVisible = it => it && it.rep.length < 3;
const itemPub = (id, it) => { const o = { id, name: it.name, slot: it.slot, owner: it.owner, price: it.price, sales: it.sales }; if (it.parts) o.parts = it.parts; if (it.tex) o.tx = 1; return o };
(function normalizeItems() { const m = nul(); for (const id of Object.keys(DB.items)) { const it = normItem(id, DB.items[id]); if (it) { m[id] = it; if (DB.accounts[it.owner.toLowerCase()]) OWN_FREE[id] = 1 } } DB.items = m })();
const itemUsable = (a, k, key) => { const id = key.slice(2), it = Object.hasOwn(DB.items, id) ? DB.items[id] : null; return it && itemVisible(it) && (k === it.slot) && (it.owner.toLowerCase() === a.nick.toLowerCase() || it.price === 0 || a.owned.includes(key)) ? it : null };

H['item.create'] = async (ws, m) => {
  const a = need(ws); rateUser(ws, 'icre', 0.05, 8);
  const slot = m.slot; if (typeof slot !== 'string' || !ISLOTS.has(slot)) throw new Err('Неизвестный тип вещи.');
  const mine = Object.values(DB.items).filter(i => i.owner.toLowerCase() === ws.u).length;
  if (mine >= MAX_ITEMS_PER_USER) throw new Err('Достигнут лимит вещей (' + MAX_ITEMS_PER_USER + ').');
  const name = clean(m.name, 30); if (!name) throw new Err('Введи название вещи.');
  const raw = { name, slot, owner: a.nick, price: m.price, created: Date.now(), parts: m.parts, tex: m.tex };
  const it = normItem('x', raw); if (!it) throw new Err(slot === 'shirt' || slot === 'pants' ? 'Нужна картинка PNG или JPG (до ~60 КБ).' : 'Некорректная форма вещи.');
  let id; do { id = 'i' + crypto.randomBytes(6).toString('hex') } while (DB.items[id]);
  DB.items[id] = it; OWN_FREE[id] = 1; dirty('i', id); return itemPub(id, it);
};
H['item.list'] = async (ws, m) => {
  need(ws); rateUser(ws, 'ilist', 2, 8);
  const scope = m.scope === 'mine' ? 'mine' : m.scope === 'owned' ? 'owned' : 'all', a = DB.accounts[ws.u];
  const slot = typeof m.slot === 'string' && ISLOTS.has(m.slot) ? m.slot : null;
  let ids = Object.keys(DB.items).filter(id => { const it = DB.items[id]; if (slot && it.slot !== slot) return false; if (scope === 'mine') return it.owner.toLowerCase() === ws.u; if (scope === 'owned') return a.owned.includes('u:' + id); return itemVisible(it) });
  ids.sort((x, y) => DB.items[y].created - DB.items[x].created);
  const page = Math.max(0, Math.floor(+m.page || 0)); ids = ids.slice(page * 48, page * 48 + 49);
  const more = ids.length > 48; return { items: ids.slice(0, 48).map(id => itemPub(id, DB.items[id])), more };
};
H['item.get'] = async (ws, m) => {
  need(ws); rateUser(ws, 'iget', 5, 15);
  const out = []; for (const id of (Array.isArray(m.ids) ? m.ids.slice(0, 24) : [])) { if (typeof id === 'string' && Object.hasOwn(DB.items, id)) { const it = DB.items[id]; if (itemVisible(it) || it.owner.toLowerCase() === ws.u) out.push(itemPub(id, it)) } }
  return { items: out };
};
H['item.delete'] = async (ws, m) => {
  need(ws); const id = typeof m.item === 'string' ? m.item : '';
  if (!Object.hasOwn(DB.items, id) || DB.items[id].owner.toLowerCase() !== ws.u) throw new Err('Вещь не найдена.');
  delete DB.items[id]; delete OWN_FREE[id]; dirty('i', id); return 1;
};

// ---------- Toolbox: ассеты игроков (скрипты, анимации, предметы) ----------
const ASSET_TYPES = new Set(['script', 'anim', 'model']), MAX_ASSETS_PER_USER = 100;
const assetPub = (id, a, ws) => ({ id, type: a.type, name: a.name, desc: a.desc || '', owner: a.owner, uses: a.uses || 0, created: a.created, mine: !!ws && a.owner.toLowerCase() === ws.u });
H['asset.publish'] = async (ws, m) => {
  const a = need(ws); rateUser(ws, 'apub', 0.05, 6);
  const type = m.type; if (!ASSET_TYPES.has(type)) throw new Err('Неизвестный тип ассета.');
  if (Object.values(DB.assets).filter(x => x.owner.toLowerCase() === ws.u).length >= MAX_ASSETS_PER_USER) throw new Err('Слишком много ваших ассетов (максимум ' + MAX_ASSETS_PER_USER + ').');
  const name = clean(m.name, 40); if (!name) throw new Err('Нужно название.');
  let data;
  if (type === 'script') {
    if (!m.data || typeof m.data.code !== 'string' || !m.data.code.trim()) throw new Err('Пустой скрипт.');
    if (m.data.code.length > MAX_LUA) throw new Err('Скрипт слишком длинный.');
    data = { code: m.data.code };
  } else if (type === 'anim') {
    const an = cleanAnims([m.data])[0]; if (!an || !an.kf.length) throw new Err('В анимации нет ключевых кадров.'); data = an;
  } else {
    const arr = cleanObjs(m.data, true).filter(o => !o.base); if (!arr.length) throw new Err('Нечего публиковать.');
    if (arr.length > 300) throw new Err('Слишком много объектов (максимум 300).'); data = arr;
  }
  const json = JSON.stringify(data); if (json.length > MAX_CONTENT) throw new Err('Ассет слишком большой.');
  let id; do { id = 't' + crypto.randomBytes(6).toString('hex') } while (DB.assets[id]);
  DB.assets[id] = { type, name, desc: clean(m.desc, 200), owner: a.nick, created: Date.now(), uses: 0, data: json };
  dirty('t', id); return assetPub(id, DB.assets[id], ws);
};
H['asset.list'] = async (ws, m) => {
  need(ws); rateUser(ws, 'alist', 2, 8);
  const type = ASSET_TYPES.has(m.type) ? m.type : '', q = typeof m.q === 'string' ? m.q.trim().toLowerCase().slice(0, 40) : '', mine = m.scope === 'mine';
  const ids = Object.keys(DB.assets).filter(id => { const a = DB.assets[id]; if (type && a.type !== type) return false; if (mine && a.owner.toLowerCase() !== ws.u) return false; return !q || (a.name + ' ' + (a.desc || '') + ' ' + a.owner).toLowerCase().includes(q) });
  ids.sort((x, y) => m.sort === 'pop' ? (DB.assets[y].uses - DB.assets[x].uses) || (DB.assets[y].created - DB.assets[x].created) : DB.assets[y].created - DB.assets[x].created);
  return { items: ids.slice(0, 48).map(id => assetPub(id, DB.assets[id], ws)), more: ids.length > 48 };
};
H['asset.get'] = async (ws, m) => {
  need(ws); rateUser(ws, 'aget', 1, 10);
  const id = typeof m.id === 'string' ? m.id : ''; if (!Object.hasOwn(DB.assets, id)) throw new Err('Ассет не найден.');
  const a = DB.assets[id]; if (a.owner.toLowerCase() !== ws.u) { a.uses = (a.uses || 0) + 1; dirty('t', id) }
  return { ...assetPub(id, a, ws), data: JSON.parse(a.data) };
};
H['asset.delete'] = async (ws, m) => {
  need(ws); const id = typeof m.id === 'string' ? m.id : '';
  if (!Object.hasOwn(DB.assets, id) || DB.assets[id].owner.toLowerCase() !== ws.u) throw new Err('Ассет не найден.');
  delete DB.assets[id]; dirty('t', id); return 1;
};
H['item.report'] = async (ws, m) => {
  need(ws); rateUser(ws, 'irep', 0.1, 5); const id = typeof m.item === 'string' ? m.item : '';
  if (!Object.hasOwn(DB.items, id)) throw new Err('Вещь не найдена.');
  const it = DB.items[id]; if (it.owner.toLowerCase() === ws.u) throw new Err('Нельзя пожаловаться на свою вещь.');
  if (!it.rep.includes(ws.u)) { it.rep.push(ws.u); dirty('i', id); pushRep({ kind: 'item', from: ws.u, target: String(it.name || id), ref: id, reason: 'Жалоба на вещь', text: '' }) }
  return 1;
};

// ===================== жалобы и панель администратора =====================
function pushRep(o) { DB.reports.push({ id: Date.now().toString(36) + Math.random().toString(36).slice(2, 6), t: Date.now(), status: 'open', ...o }); if (DB.reports.length > 500) DB.reports.splice(0, DB.reports.length - 500); save() }
const adm = ws => { need(ws); if (!ADMINS.has(ws.u)) throw new Err('Нет доступа.') };
H['report.send'] = async (ws, m) => {
  const a = need(ws); rateUser(ws, 'rsend', 0.05, 4);
  const t = clean(String(m.target || ''), 40), r = clean(String(m.reason || ''), 60), x = clean(String(m.text || ''), 300);
  if (!t) throw new Err('Не выбран игрок.');
  pushRep({ kind: 'player', from: a.nick, target: t, reason: r, text: x }); return 1;
};
H['admin.reports'] = async ws => { adm(ws); return { reports: DB.reports.slice().reverse().slice(0, 200) } };
H['admin.report.set'] = async (ws, m) => {
  adm(ws); const i = DB.reports.findIndex(x => x.id === m.id); if (i < 0) throw new Err('Жалоба не найдена.');
  if (m.del) DB.reports.splice(i, 1); else DB.reports[i].status = m.status === 'open' ? 'open' : 'done';
  save(); return 1;
};
H['admin.find'] = async (ws, m) => {
  adm(ws); const q = String(m.q || '').trim().toLowerCase().slice(0, 40);
  const users = Object.keys(DB.accounts).filter(k => !q || k.includes(q)).slice(0, 30).map(k => { const a = DB.accounts[k]; return { nick: a.nick, coins: a.coins, ban: banActive(a) ? { until: a.ban.until, reason: a.ban.reason } : null } });
  const places = Object.keys(DB.places).filter(id => { const p = DB.places[id]; return !q || String(p.name).toLowerCase().includes(q) || String(p.owner).toLowerCase().includes(q) }).slice(0, 30).map(id => ({ id, name: DB.places[id].name, owner: DB.places[id].owner }));
  return { users, places };
};
H['admin.coins'] = async (ws, m) => {
  adm(ws); const key = String(m.nick || '').toLowerCase(), a = Object.hasOwn(DB.accounts, key) ? DB.accounts[key] : null; if (!a) throw new Err('Игрок не найден.');
  const n = Math.floor(+m.amount); if (!Number.isFinite(n) || n < 0 || n > 1e9) throw new Err('Количество: от 0 до 1 000 000 000.');
  a.coins = Math.max(0, m.mode === 'take' ? a.coins - n : m.mode === 'set' ? n : a.coins + n); dirty('a', key); return { coins: a.coins };
};
H['admin.ban'] = async (ws, m) => {
  adm(ws); const key = String(m.nick || '').toLowerCase(), a = Object.hasOwn(DB.accounts, key) ? DB.accounts[key] : null; if (!a) throw new Err('Игрок не найден.');
  if (ADMINS.has(key)) throw new Err('Администратора забанить нельзя.');
  const h = Math.max(0, Math.min(24 * 3650, +m.hours || 0));
  a.ban = { until: h ? Date.now() + h * 36e5 : 0, reason: clean(String(m.reason || 'не указана'), 200), by: ws.u, at: Date.now() };
  for (const k of Object.keys(DB.sessions)) if (DB.sessions[k].u === key) { delete DB.sessions[k]; dirty('s', k) }
  dirty('a', key); return 1;
};
H['admin.unban'] = async (ws, m) => {
  adm(ws); const key = String(m.nick || '').toLowerCase(); if (!Object.hasOwn(DB.accounts, key)) throw new Err('Игрок не найден.');
  delete DB.accounts[key].ban; dirty('a', key); return 1;
};
H['admin.place.delete'] = async (ws, m) => {
  adm(ws); const id = strId(m.id); if (!id || !Object.hasOwn(DB.places, id)) throw new Err('Плейс не найден.');
  delete DB.places[id]; dirty('p', id); placesChanged(); return 1;
};

H.shop = async (ws, m) => {
  const a = need(ws); rateUser(ws, 'shop', 3, 6);
  const k = m.k, val = m.val === undefined ? null : m.val;
  if (k === 'hc') {
    if (val === null) delete a.eq.hc;
    else if (typeof val === 'string' && /^#[0-9a-f]{6}$/i.test(val)) a.eq.hc = val.toLowerCase();
    else throw new Err('Неверный цвет волос.');
    dirty('a', ws.u); return pub(a);
  }
  if (!['sh', 'hat', 'hair', 'acc', 'shirt', 'pants'].includes(k)) throw new Err('Неизвестный товар.');
  if (val === null) { delete a.eq[k]; dirty('a', ws.u); return pub(a) }
  if (typeof val === 'string' && UKEY.test(val)) {          // вещь, созданная игроком
    const id = val.slice(2), it = Object.hasOwn(DB.items, id) ? DB.items[id] : null;
    if (!it || !itemVisible(it) || it.slot !== k) throw new Err('Вещь не найдена.');
    const own = it.owner.toLowerCase() === ws.u;
    if (!own && it.price > 0 && !a.owned.includes(val)) {
      if (a.coins < it.price) throw new Err('Не хватает монет.');
      a.coins -= it.price; a.owned.push(val); it.sales++; dirty('i', id);
      const cr = DB.accounts[it.owner.toLowerCase()]; if (cr) { cr.coins += Math.floor(it.price * 0.7); dirty('a', it.owner.toLowerCase()) }
    }
    a.eq[k] = val; dirty('a', ws.u); return pub(a);
  }
  const it = typeof val === 'string' ? shopItem(k, val) : null;
  if (!it) throw new Err('Неизвестный товар.');
  const key = shopKey(k, val);
  if (it[2] > 0 && !a.owned.includes(key)) {
    if (a.coins < it[2]) throw new Err('Не хватает монет.');
    a.coins -= it[2]; a.owned.push(key);
  }
  a.eq[k] = val;
  dirty('a', ws.u); return pub(a);
};

// ----- яйца: всё считает сервер (бросок, цена, монеты). Клиент только просит «открыть 1 или 3». -----
H['egg.info'] = async () => ({ price: EGG.price, total: EGG_W, pets: EGG.pets.map(p => ({ id: p.id, n: p.n, e: p.e, r: p.r, w: p.w })) });
H['egg.hatch'] = async (ws, m) => {
  const a = need(ws); rateUser(ws, 'egg', 2, 6);
  const n = m.n === 1 ? 1 : m.n === 3 ? 3 : 0; if (!n) throw new Err('Неверное количество яиц.');
  const cost = EGG.price * n; if (a.coins < cost) throw new Err('Не хватает монет.');
  a.pets = a.pets || nul(); a.seen = a.seen || [];
  a.coins -= cost; const results = [];
  for (let i = 0; i < n; i++) {
    const p = rollPet(); if (!a.seen.includes(p.id)) a.seen.push(p.id);
    const del = a.adel === true && p.r === 'Common';
    if (!del) a.pets[p.id] = (a.pets[p.id] || 0) + 1;
    results.push({ id: p.id, del });
  }
  dirty('a', ws.u); return { results, me: pub(a) };
};
H['egg.set'] = async (ws, m) => { const a = need(ws); rateUser(ws, 'eggs', 2, 10); a.adel = m.adel === true; dirty('a', ws.u); return pub(a) };

H.sub = async ws => { need(ws); if (!take('sub:' + ws.u, 0.5, 5)) throw new Err('Слишком часто.'); ws.subs = true; send(ws, snapFor(ws)); return 1 };
H.unsub = async ws => { ws.subs = false; return 1 };

H['place.get'] = async (ws, m) => {
  need(ws); rateUser(ws, 'pget', 3, 15);
  const id = strId(m.place), p = id && Object.hasOwn(DB.places, id) ? DB.places[id] : null;
  if (!p) throw new Err('Плейс не найден.');
  const out = { id, name: p.name, owner: p.owner, objs: p.objs, scripts: p.scripts, col: p.col || [], rev: p.rev || 0 };
  if (p.blocks) out.blocks = p.blocks;
  return out;
};

H['place.create'] = async (ws, m) => {
  const a = need(ws); rateUser(ws, 'pnew', 0.3, 2);
  const name = clean(m.name, 30); if (!name) throw new Err('Введи название плейса.');
  const desc = clean(m.desc, 400);
  const mine = Object.values(DB.places).filter(p => p.owner.toLowerCase() === ws.u).length;
  if (mine >= MAX_PLACES_PER_USER) throw new Err('Достигнут лимит плейсов (' + MAX_PLACES_PER_USER + ').');
  const c = cleanContent(m.objs, m.scripts, true);
  let id; do { id = 'p' + Date.now().toString(36) + crypto.randomBytes(4).toString('hex') } while (DB.places[id]);
  const now = Date.now();
  DB.places[id] = { name, desc, owner: a.nick, plays: 0, created: now, updated: now, objs: c.objs, scripts: c.scripts };
  dirty('p', id); placesChanged(); return { id };
};

H['place.save'] = async (ws, m) => {
  need(ws); rateUser(ws, 'psave', 0.7, 3);
  const id = strId(m.place), p = id && Object.hasOwn(DB.places, id) ? DB.places[id] : null;
  if (!p) throw new Err('Плейс не найден.');
  const col = p.col || [];
  if (p.owner.toLowerCase() !== ws.u && !col.includes(ws.u)) throw new Err('Это не твой плейс.');
  if (col.length && m.force !== true && m.rev !== undefined && m.rev !== (p.rev || 0)) throw new Err('Соавтор уже сохранил новую версию плейса.', 'conflict');
  const c = cleanContent(m.objs, m.scripts, true);
  p.objs = c.objs; p.scripts = c.scripts; p.updated = Date.now(); p.rev = (p.rev || 0) + 1; delete p.blocks;
  dirty('p', id); placesChanged(); return { rev: p.rev };
};

H['place.icon'] = async (ws, m) => {
  need(ws); rateUser(ws, 'pico', 0.2, 3);
  const id = strId(m.place), p = id && Object.hasOwn(DB.places, id) ? DB.places[id] : null;
  if (!p) throw new Err('Плейс не найден.');
  if (p.owner.toLowerCase() !== ws.u) throw new Err('Это не твой плейс.');
  if (m.icon === null) { delete p.icon; delete p.iconV }
  else {
    if (typeof m.icon !== 'string' || m.icon.length > 120000) throw new Err('Картинка слишком большая (макс. ~90 КБ).');
    const x = ICON_RE.exec(m.icon); if (!x) throw new Err('Нужна картинка JPG, PNG или WebP.');
    const b = Buffer.from(x[2], 'base64'), t = x[1];
    const good = t === 'jpeg' ? (b[0] === 0xff && b[1] === 0xd8) : t === 'png' ? (b[0] === 0x89 && b[1] === 0x50) : (b.subarray(0, 4).toString() === 'RIFF' && b.subarray(8, 12).toString() === 'WEBP');
    if (!good) throw new Err('Файл не похож на картинку.');
    p.icon = m.icon; p.iconV = Date.now();
  }
  dirty('p', id); placesChanged(); return { v: p.iconV || 0 };
};

H['place.delete'] = async (ws, m) => {
  need(ws); rateUser(ws, 'pdel', 0.5, 3);
  const id = strId(m.place), p = id && Object.hasOwn(DB.places, id) ? DB.places[id] : null;
  if (!p) throw new Err('Плейс не найден.');
  if (p.owner.toLowerCase() !== ws.u) throw new Err('Это не твой плейс.');
  delete DB.places[id]; dirty('p', id); placesChanged(); return 1;
};

H['place.play'] = async (ws, m) => {
  need(ws); rateUser(ws, 'pplay', 1, 5);
  const id = strId(m.place), p = id && Object.hasOwn(DB.places, id) ? DB.places[id] : null;
  if (!p) return 0;
  if (p.owner.toLowerCase() === ws.u) return 0;                 // свои запуски не накручивают рейтинг
  const k = ws.u + '|' + id, last = playSeen.get(k) || 0;
  if (Date.now() - last < 36e5) return 0;                       // один запуск от игрока в час
  playSeen.set(k, Date.now()); p.plays++; dirty('p', id); placesChanged(); return 1;
};

H['place.details'] = async (ws, m) => {
  need(ws); rateUser(ws, 'pdet', 3, 15);
  const id = strId(m.place), p = id && Object.hasOwn(DB.places, id) ? DB.places[id] : null;
  if (!p) throw new Err('Плейс не найден.');
  const servers = []; let online = 0;
  for (const k of PLACE_ROOMS.get(id) || []) { const mt = RMETA.get(k), n = rooms.get(k).size; online += n; if (!mt.priv) servers.push({ i: mt.inst, n, max: MAX_ROOM }) }
  servers.sort((a, b) => b.n - a.n);
  return { id, name: p.name, owner: p.owner, col: (p.col || []).map(nickOf), pend: p.owner.toLowerCase() === ws.u ? (p.inv || []).map(nickOf) : [], desc: p.desc || '', plays: p.plays, created: p.created, updated: p.updated, ic: p.icon ? p.iconV || 1 : 0, online, servers: servers.slice(0, 20), max: MAX_ROOM };
};
H['place.info'] = async (ws, m) => {
  need(ws); rateUser(ws, 'pinfo', 0.5, 3);
  const id = strId(m.place), p = id && Object.hasOwn(DB.places, id) ? DB.places[id] : null;
  if (!p) throw new Err('Плейс не найден.');
  if (p.owner.toLowerCase() !== ws.u) throw new Err('Это не твой плейс.');
  if (m.name !== undefined) { const n = clean(m.name, 30); if (!n) throw new Err('Введи название.'); p.name = n }
  if (m.desc !== undefined) p.desc = clean(m.desc, 400);
  p.updated = Date.now(); dirty('p', id); placesChanged(); return { name: p.name, desc: p.desc || '' };
};
H['server.find'] = async (ws, m) => {
  need(ws); if (!take('find:' + ws.ip, 0.3, 8)) throw new Err('Слишком часто, подожди.');
  const k = typeof m.code === 'string' ? CODES.get(m.code.toUpperCase().replace(/[^A-Z0-9]/g, '')) : null, mt = k && RMETA.get(k);
  if (!mt || !Object.hasOwn(DB.places, mt.place)) throw new Err('Сервер с таким кодом не найден или уже закрыт.', 'closed');
  return { place: mt.place };
};

H.join = async (ws, m) => {
  need(ws); rateUser(ws, 'join', 1, 5);
  const id = strId(m.room); if (!id || !Object.hasOwn(DB.places, id)) throw new Err('Плейс не найден.');
  const want = typeof m.code === 'string' && m.code ? m.code.toUpperCase().replace(/[^A-Z0-9]/g, '') : null;
  if (want && !take('code:' + ws.ip, 0.5, 10)) throw new Err('Слишком много попыток, подожди.');
  let fkey = null;                                       // вход к другу: через его профиль или приглашение
  if (typeof m.friend === 'string' && m.friend) {
    const fk = m.friend.toLowerCase();
    if (!fArr(DB.accounts[ws.u]).fr.includes(fk)) throw new Err('Этого игрока нет в твоих друзьях.');
    const fw = socketsOf(fk).find(w => w.room && RMETA.get(w.room) && RMETA.get(w.room).place === id);
    if (!fw) throw new Err('Друг уже ушёл с этого сервера.', 'closed');
    fkey = fw.room;
  }
  leaveRoom(ws);
  let key = fkey;
  if (fkey) { /* к другу */ } else if (want) {                                            // вход к другу по коду
    key = CODES.get(want); const mt = key && RMETA.get(key);
    if (!mt || mt.place !== id) throw new Err('Сервер с таким кодом не найден или уже закрыт.', 'closed');
  } else if (typeof m.inst === 'string' && m.inst) {     // конкретный публичный сервер из списка
    key = id + '|' + m.inst.slice(0, 12); const mt = RMETA.get(key);
    if (!mt || mt.priv) throw new Err('Этот сервер уже закрыт.', 'closed');
  } else if (m.priv === true) key = mkRoom(id, true);    // новый частный сервер для друзей
  else {                                                 // автоподбор: самый заполненный из неполных публичных, иначе новый
    let best = null;
    for (const k of PLACE_ROOMS.get(id) || []) { const n = rooms.get(k).size; if (!RMETA.get(k).priv && n < MAX_ROOM && (!best || n > best[1])) best = [k, n] }
    key = best ? best[0] : mkRoom(id, false);
  }
  let S = rooms.get(key);
  if (S.size >= MAX_ROOM) { if (!S.size) dropRoom(key); throw new Err('Сервер заполнен (макс. ' + MAX_ROOM + ' игроков).', 'full') }
  S.add(ws); ws.room = key; ws.pres = null; dirtyRooms.add(key);
  const mt = RMETA.get(key);
  return { pid: ws.pid, inst: mt.inst, priv: mt.priv, code: mt.code };
};
H.leave = async ws => { leaveRoom(ws); return 1 };

function presEq(a) { const e = {}; for (const k of ['sh', 'hat', 'hair', 'acc', 'shirt', 'pants']) { const v = a.eq[k]; if (!v) continue; if (UKEY.test(v)) { const it = DB.items[v.slice(2)]; if (it && itemVisible(it)) e[k] = v } else e[k] = v } return e }
H.pres = async (ws, m) => {
  const a = need(ws); if (!ws.room) return 0;
  const d = m.data; if (!d || typeof d !== 'object') return 0;
  if (typeof d.x !== 'number' || typeof d.y !== 'number' || typeof d.z !== 'number' || typeof d.r !== 'number') return 0;   // null/строки не принимаем
  const x = d.x, y = d.y, z = d.z, r = d.r;
  if (![x, y, z, r].every(Number.isFinite) || Math.abs(x) > 1e4 || Math.abs(z) > 1e4 || y < -200 || y > 2000 || Math.abs(r) > 100) return 0;
  ws.pres = { x, y, z, r, mv: !!d.mv, n: a.nick, e: presEq(a), w: BIN_TYPES.has(d.w) ? d.w : null };   // имя и одежда — из аккаунта
  dirtyRooms.add(ws.room); return 1;
};

H.emit = async (ws, m) => {
  const a = need(ws); if (!ws.room) return 0;
  if (m.topic !== 'chat') throw new Err('Неизвестное событие.');
  const text = clean(m.data && m.data.t, 120); if (!text) return 0;
  if (!take('chat:' + ws.u, 1.5, 4)) throw new Err('Не так быстро!');
  const msg = JSON.stringify({ t: 'ev', topic: 'chat', data: { n: a.nick, t: text }, from: ws.pid });
  for (const w of rooms.get(ws.room) || []) if (w !== ws) send(w, msg);
  return 1;
};

// ===================== друзья =====================
const MAX_FR = 200, MAX_INC = 50, MAX_COL = 5;
const fArr = a => { for (const k of ['fr', 'inc', 'out']) if (!Array.isArray(a[k])) a[k] = []; return a };
const rm = (arr, x) => { const i = arr.indexOf(x); if (i >= 0) arr.splice(i, 1); return i >= 0 };
const nickOf = k => DB.accounts[k] ? DB.accounts[k].nick : k;
const socketsOf = key => { const r = []; for (const w of wss.clients) if (w.u === key) r.push(w); return r };
function notify(key, o) { const s = JSON.stringify({ t: 'notif', ...o }); for (const w of socketsOf(key)) send(w, s) }
function targetOf(m, ws) {
  const nick = typeof m.nick === 'string' ? m.nick.trim() : '', key = nick.toLowerCase();
  if (!nick || !Object.hasOwn(DB.accounts, key)) throw new Err('Игрок с таким ником не найден.');
  if (key === ws.u) throw new Err('Это ты сам 🙂');
  return [key, fArr(DB.accounts[key])];
}
function statusOf(key) {
  const ws = socketsOf(key).sort((x, y) => (y.room ? 1 : 0) - (x.room ? 1 : 0))[0];
  if (!ws) return { on: 0 };
  const mt = ws.room && RMETA.get(ws.room);
  if (!mt || !Object.hasOwn(DB.places, mt.place)) return { on: 1 };
  return { on: 1, place: mt.place, pn: DB.places[mt.place].name, full: rooms.get(ws.room).size >= MAX_ROOM };
}
function flist(key) {
  const a = fArr(DB.accounts[key]), ok = k => DB.accounts[k];
  const collab = []; for (const id of Object.keys(DB.places)) { const p = DB.places[id]; if (p.inv && p.inv.includes(key)) collab.push({ place: id, pn: p.name, from: p.owner }) }
  return {
    friends: a.fr.filter(ok).map(k => ({ nick: nickOf(k), ...statusOf(k) })).sort((x, y) => y.on - x.on || x.nick.localeCompare(y.nick)),
    inc: a.inc.filter(ok).map(nickOf), out: a.out.filter(ok).map(nickOf), collab: collab.slice(0, 20)
  };
}
function makeFriends(ka, a, kb, b) {
  rm(a.inc, kb); rm(a.out, kb); rm(b.inc, ka); rm(b.out, ka);
  if (!a.fr.includes(kb)) a.fr.push(kb);
  if (!b.fr.includes(ka)) b.fr.push(ka);
  dirty('a', ka); dirty('a', kb);
  notify(kb, { kind: 'faccept', from: a.nick });
}
H['friend.list'] = async ws => { need(ws); rateUser(ws, 'flist', 2, 8); return flist(ws.u) };
H['friend.add'] = async (ws, m) => {
  const a = fArr(need(ws)); rateUser(ws, 'fadd', 0.5, 5);
  const [key, t] = targetOf(m, ws);
  if (a.fr.includes(key)) throw new Err('Вы уже друзья.');
  if (a.out.includes(key)) throw new Err('Запрос уже отправлен.');
  if (a.inc.includes(key)) { makeFriends(ws.u, a, key, t); return { state: 'friends', ...flist(ws.u) } }   // он уже звал нас — просто дружим
  if (a.fr.length >= MAX_FR) throw new Err('У тебя максимум друзей (' + MAX_FR + ').');
  if (a.out.length >= MAX_INC) throw new Err('Слишком много неотвеченных запросов.');
  if (t.inc.length >= MAX_INC) throw new Err('У этого игрока слишком много запросов.');
  a.out.push(key); t.inc.push(ws.u); dirty('a', ws.u); dirty('a', key);
  notify(key, { kind: 'freq', from: a.nick });
  return { state: 'sent', ...flist(ws.u) };
};
H['friend.respond'] = async (ws, m) => {
  const a = fArr(need(ws)); rateUser(ws, 'fresp', 2, 8);
  const [key, t] = targetOf(m, ws);
  if (!a.inc.includes(key)) throw new Err('Этого запроса уже нет.');
  if (m.accept === true) { if (a.fr.length >= MAX_FR) throw new Err('У тебя максимум друзей.'); makeFriends(ws.u, a, key, t) }
  else { rm(a.inc, key); rm(t.out, ws.u); dirty('a', ws.u); dirty('a', key) }
  return flist(ws.u);
};
H['friend.remove'] = async (ws, m) => {   // удалить из друзей или отменить свой запрос
  const a = fArr(need(ws)); rateUser(ws, 'frem', 2, 8);
  const [key, t] = targetOf(m, ws);
  rm(a.fr, key); rm(t.fr, ws.u); rm(a.out, key); rm(t.inc, ws.u);
  dirty('a', ws.u); dirty('a', key); return flist(ws.u);
};
H['friend.invite'] = async (ws, m) => {   // позвать друга на свой сервер
  const a = fArr(need(ws)); rateUser(ws, 'finv', 1, 6);
  const [key] = targetOf(m, ws);
  if (!a.fr.includes(key)) throw new Err('Этого игрока нет в твоих друзьях.');
  if (!take('finv:' + ws.u + ':' + key, 0.1, 2)) throw new Err('Ты уже недавно звал этого друга.');
  if (!socketsOf(key).length) throw new Err('Друг сейчас не в сети.');
  const mt = ws.room && RMETA.get(ws.room);
  if (!mt || !Object.hasOwn(DB.places, mt.place)) throw new Err('Сначала зайди на сервер.');
  notify(key, { kind: 'invite', from: a.nick, place: mt.place, pn: DB.places[mt.place].name });
  return 1;
};
H['place.collab'] = async (ws, m) => {   // автор зовёт друга делать плейс вместе / убирает соавтора / соавтор уходит сам
  const a = fArr(need(ws)); rateUser(ws, 'pcol', 1, 6);
  const id = strId(m.place), p = id && Object.hasOwn(DB.places, id) ? DB.places[id] : null;
  if (!p) throw new Err('Плейс не найден.');
  p.col = p.col || []; p.inv = p.inv || [];
  const owner = p.owner.toLowerCase() === ws.u, nick = typeof m.nick === 'string' ? m.nick.trim() : '', key = nick.toLowerCase();
  if (m.remove) {
    if (!owner && key !== ws.u) throw new Err('Нет прав.');
    rm(p.col, key); rm(p.inv, key); dirty('p', id); placesChanged();
    return { col: p.col.map(nickOf), pend: p.inv.map(nickOf) };
  }
  if (!owner) throw new Err('Звать соавторов может только автор плейса.');
  if (!Object.hasOwn(DB.accounts, key) || key === ws.u) throw new Err('Игрок не найден.');
  if (!a.fr.includes(key)) throw new Err('Соавтором можно сделать только друга.');
  if (p.col.includes(key)) throw new Err('Он уже соавтор.');
  if (p.col.length + p.inv.length >= MAX_COL) throw new Err('Максимум соавторов: ' + MAX_COL + '.');
  if (!p.inv.includes(key)) p.inv.push(key);
  dirty('p', id); notify(key, { kind: 'collab', from: a.nick, place: id, pn: p.name });
  return { col: p.col.map(nickOf), pend: p.inv.map(nickOf) };
};
H['place.collab.respond'] = async (ws, m) => {
  const a = need(ws); rateUser(ws, 'pcr', 1, 6);
  const id = strId(m.place), p = id && Object.hasOwn(DB.places, id) ? DB.places[id] : null;
  if (!p || !p.inv || !p.inv.includes(ws.u)) throw new Err('Приглашения уже нет.');
  rm(p.inv, ws.u); p.col = p.col || [];
  if (m.accept === true) {
    if (p.col.length >= MAX_COL) throw new Err('У плейса уже максимум соавторов.');
    p.col.push(ws.u); notify(p.owner.toLowerCase(), { kind: 'caccept', from: a.nick, pn: p.name });
  }
  dirty('p', id); placesChanged(); return flist(ws.u);
};

// ===================== соединения =====================
const QUIET = new Set(['pres']);   // на эти сообщения ответ не нужен, если нет id
wss.on('connection', ws => {
  totalConn++; ipConns.set(ws.ip, (ipConns.get(ws.ip) || 0) + 1);
  ws.pid = 'p' + (++nPid); ws.u = null; ws.sh = null; ws.subs = false; ws.room = null; ws.pres = null; ws.alive = true; ws.born = Date.now(); ws.strikes = 0;
  ws.on('pong', () => { ws.alive = true });
  ws.on('error', () => { });
  ws.on('message', (raw, isBin) => {
    ws.alive = true;
    if (isBin) return;
    if (!take('m:' + ws.pid, 40, 80)) { if (++ws.strikes > 20) ws.close(1008, 'rate'); return }
    if (!ws.u && raw.length > 2048) return ws.close(1009, 'big');
    let m; try { m = JSON.parse(raw) } catch { return }
    if (!m || typeof m !== 'object' || Array.isArray(m) || typeof m.t !== 'string') return;
    const hasId = typeof m.id === 'number' || (typeof m.id === 'string' && m.id.length <= 20);
    const reply = o => { if (hasId) send(ws, { id: m.id, ...o }) };
    const h = H[m.t]; if (!h) return reply({ ok: false, err: 'Неизвестная команда.' });
    Promise.resolve().then(() => h(ws, m)).then(
      res => { if (hasId || !QUIET.has(m.t)) reply({ ok: true, res: res === undefined ? null : res }) },
      e => {
        if (e instanceof Err) reply({ ok: false, err: e.message, code: e.code });
        else { log('Ошибка в', m.t + ':', e && e.stack || e); reply({ ok: false, err: 'Ошибка сервера.' }) }
      });
  });
  ws.on('close', () => {
    totalConn--; const n = (ipConns.get(ws.ip) || 1) - 1; if (n > 0) ipConns.set(ws.ip, n); else ipConns.delete(ws.ip);
    leaveRoom(ws);
  });
});

// секьюрность соединений: HTTPS-статус берём из заголовка апгрейда
const _handleUpgrade = wss.handleUpgrade.bind(wss);
wss.handleUpgrade = (req, sock, head, cb) => _handleUpgrade(req, sock, head, ws => { ws.secure = isSecure(req); cb(ws) });

setInterval(() => {   // убираем «мёртвые» соединения
  const now = Date.now();
  for (const ws of wss.clients) {
    if (!ws.alive) { ws.terminate(); continue }
    if (!ws.u && now - ws.born > 10 * 60e3) { ws.close(1000, 'idle'); continue }
    ws.alive = false; try { ws.ping() } catch { }
  }
}, 30e3).unref();

// ===================== запуск / остановка =====================
process.on('uncaughtException', e => log('uncaughtException:', e && e.stack || e));
process.on('unhandledRejection', e => log('unhandledRejection:', e && e.stack || e));
let closing = false;
function shutdown() { if (closing) return; closing = true; log('Остановка, сохраняю данные…'); flushSync(); process.exit(0) }
process.on('SIGINT', shutdown); process.on('SIGTERM', shutdown);

if (require.main === module) {
  srv.listen(PORT, () => log('VoxelBlox: http://localhost:' + PORT + '  (аккаунтов: ' + Object.keys(DB.accounts).length + ', плейсов: ' + Object.keys(DB.places).length + ')'));
}
module.exports = { srv, wss, DB, flushSync };

