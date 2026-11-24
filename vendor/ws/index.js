'use strict';
// Минимальная реализация WebSocket-сервера (RFC 6455) — чтобы не требовался npm install.
// Если установлен настоящий пакет `ws`, server.js берёт его, а не этот файл.
const crypto = require('crypto');
const { EventEmitter } = require('events');
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';

class WebSocket extends EventEmitter {
  constructor(sock, maxPayload) {
    super(); this.readyState = 1; this._s = sock; this._max = maxPayload; this._buf = Buffer.alloc(0); this._frag = null; this._fragOp = 0; this._fragLen = 0;
    sock.setNoDelay(true);
    sock.on('data', d => { try { this._buf = this._buf.length ? Buffer.concat([this._buf, d]) : d; this._parse() } catch (e) { this._fail(1002) } });
    sock.on('close', () => this._closed()); sock.on('error', () => { try { sock.destroy() } catch { } });
  }
  get bufferedAmount() { return this._s.writableLength }
  _closed() { if (this.readyState === 3) return; this.readyState = 3; this.emit('close') }
  _frame(op, payload) {
    const n = payload.length; let h;
    if (n < 126) { h = Buffer.alloc(2); h[1] = n } else if (n < 65536) { h = Buffer.alloc(4); h[1] = 126; h.writeUInt16BE(n, 2) } else { h = Buffer.alloc(10); h[1] = 127; h.writeBigUInt64BE(BigInt(n), 2) }
    h[0] = 0x80 | op; return Buffer.concat([h, payload]);
  }
  _write(op, payload) { if (this._s.destroyed || !this._s.writable) return; this._s.write(this._frame(op, payload)) }
  send(data) { if (this.readyState !== 1) throw new Error('WebSocket is not open'); if (typeof data === 'string') this._write(1, Buffer.from(data)); else this._write(2, Buffer.from(data)) }
  ping() { if (this.readyState === 1) this._write(9, Buffer.alloc(0)) }
  close(code = 1000) {
    if (this.readyState !== 1) return; this.readyState = 2; const p = Buffer.alloc(2); p.writeUInt16BE(code); this._write(8, p);
    setTimeout(() => this.terminate(), 3000).unref();
  }
  terminate() { this.readyState = 3; try { this._s.destroy() } catch { } this._closed() }
  _fail(code) { this.close(code); setTimeout(() => this.terminate(), 50).unref() }
  _parse() {
    for (;;) {
      const b = this._buf; if (b.length < 2) return;
      const fin = !!(b[0] & 0x80), op = b[0] & 15, masked = !!(b[1] & 0x80); let len = b[1] & 0x7f, off = 2;
      if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4 } else if (len === 127) { if (b.length < 10) return; len = Number(b.readBigUInt64BE(2)); off = 10 }
      if (!masked) return this._fail(1002);
      if (len > this._max) return this._fail(1009);
      if (b.length < off + 4 + len) return;
      const mask = b.subarray(off, off + 4), data = Buffer.from(b.subarray(off + 4, off + 4 + len));
      for (let i = 0; i < data.length; i++) data[i] ^= mask[i & 3];
      this._buf = b.subarray(off + 4 + len);
      if (op === 8) { this.close(1000); return this._s.end() }
      if (op === 9) { this._write(10, data); continue }
      if (op === 10) { this.emit('pong', data); continue }
      if (op === 1 || op === 2 || op === 0) {
        if (op !== 0) { this._fragOp = op; this._frag = []; this._fragLen = 0 }
        if (!this._frag) return this._fail(1002);
        this._frag.push(data); this._fragLen += data.length; if (this._fragLen > this._max) return this._fail(1009);
        if (fin) { const full = Buffer.concat(this._frag), isBin = this._fragOp === 2; this._frag = null; this.emit('message', isBin ? full : full, isBin) }
      }
    }
  }
}

class WebSocketServer extends EventEmitter {
  constructor(o = {}) { super(); this.clients = new Set(); this._max = o.maxPayload || 100 * 1024 * 1024 }
  handleUpgrade(req, sock, head, cb) {
    const key = req.headers['sec-websocket-key'];
    if (!key || String(req.headers.upgrade || '').toLowerCase() !== 'websocket') { sock.destroy(); return }
    const acc = crypto.createHash('sha1').update(key + GUID).digest('base64');
    sock.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + acc + '\r\n\r\n');
    const ws = new WebSocket(sock, this._max); this.clients.add(ws); ws.on('close', () => this.clients.delete(ws));
    if (head && head.length) { ws._buf = Buffer.from(head); setImmediate(() => { try { ws._parse() } catch { } }) }
    cb(ws);
  }
}
module.exports = { WebSocketServer, WebSocket };
  
