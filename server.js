'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = Number(process.env.PORT || 3000);
const HOST = process.env.HOST || '0.0.0.0';
const ROOT = path.join(__dirname, 'public');
const DATA_DIR = path.join(__dirname, 'data');
const DB_FILE = path.join(DATA_DIR, 'users.json');
fs.mkdirSync(DATA_DIR, { recursive: true });
let users = {};
try { users = JSON.parse(fs.readFileSync(DB_FILE, 'utf8')); } catch { users = {}; }
function saveUsers() { const tmp = DB_FILE + '.tmp'; fs.writeFileSync(tmp, JSON.stringify(users, null, 2)); fs.renameSync(tmp, DB_FILE); }
const sessions = new Map(); // token -> username; in-memory sessions expire when server restarts
const clients = new Map(); // ws -> {username, roomCode}
const rooms = new Map();
const queue = [];
const MAX_MESSAGE = 16 * 1024;
const randomToken = () => crypto.randomBytes(32).toString('hex');
const randomCode = () => crypto.randomBytes(3).toString('hex').toUpperCase();
const safeUser = name => users[name] ? ({ username: name, stats: users[name].stats }) : null;
const send = (ws, data) => { if (ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify(data)); };
function error(ws, message) { send(ws, { type: 'error', message }); }
function validName(name) { return typeof name === 'string' && /^[a-zA-Z0-9_ -]{3,20}$/.test(name.trim()); }
function hashPassword(password, salt = crypto.randomBytes(16).toString('hex')) {
  return new Promise((resolve, reject) => crypto.scrypt(password, salt, 64, (err, key) => err ? reject(err) : resolve({ salt, hash: key.toString('hex') })));
}
async function passwordMatches(password, record) {
  const got = await hashPassword(password, record.salt);
  const a = Buffer.from(got.hash, 'hex'), b = Buffer.from(record.hash, 'hex');
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}
function getAuth(ws, msg) {
  const token = msg.token;
  const username = sessions.get(token);
  if (!username || !users[username]) { error(ws, 'Сначала войди в аккаунт.'); return null; }
  const client = clients.get(ws);
  if (client) client.username = username;
  return username;
}
function roomSnapshot(room) {
  return { code: room.code, mode: room.mode, maxPlayers: room.maxPlayers, players: [...room.players].map(name => ({ username: name, online: [...clients.entries()].some(([ws,c]) => ws.readyState === WebSocket.OPEN && c.username === name && c.roomCode === room.code) })) };
}
function broadcastRoom(room) { const state = { type: 'room_state', room: roomSnapshot(room) }; for (const [ws,c] of clients) if (c.roomCode === room.code) send(ws, state); }
function leaveRoom(ws) {
  const c = clients.get(ws); if (!c || !c.roomCode) return;
  const room = rooms.get(c.roomCode); c.roomCode = null;
  if (room) { room.players = room.players.filter(n => n !== c.username); if (!room.players.length) rooms.delete(room.code); else broadcastRoom(room); }
  send(ws, { type: 'room_left' });
}
function enterRoom(ws, room) {
  const c = clients.get(ws); if (!c || !c.username) return error(ws, 'Сначала войди в аккаунт.');
  leaveRoom(ws);
  if (room.players.length >= room.maxPlayers) return error(ws, 'Комната заполнена.');
  if (!room.players.includes(c.username)) room.players.push(c.username);
  c.roomCode = room.code;
  broadcastRoom(room);
}
function createRoom(ws, maxPlayers = 10, mode = 'bomb') {
  const c = clients.get(ws); if (!c || !c.username) return error(ws, 'Сначала войди в аккаунт.');
  leaveRoom(ws);
  let code; do { code = randomCode(); } while (rooms.has(code));
  const room = { code, mode: mode === 'hostage' ? 'hostage' : 'bomb', maxPlayers: Math.max(2, Math.min(10, Number(maxPlayers) || 10)), players: [] };
  rooms.set(code, room); enterRoom(ws, room);
}
function sendStats(ws, username) { send(ws, { type: 'stats', stats: users[username].stats }); }
async function handle(ws, msg) {
  if (!msg || typeof msg.type !== 'string') return error(ws, 'Неверный формат сообщения.');
  if (msg.type === 'register') {
    const username = typeof msg.username === 'string' ? msg.username.trim() : '';
    const password = msg.password;
    if (!validName(username)) return error(ws, 'Имя: 3–20 символов, латиница, цифры, пробел, _ или -.');
    if (typeof password !== 'string' || password.length < 8 || password.length > 128) return error(ws, 'Пароль должен содержать 8–128 символов.');
    if (users[username]) return error(ws, 'Такое имя уже занято.');
    const pass = await hashPassword(password);
    users[username] = { ...pass, createdAt: new Date().toISOString(), stats: { matches: 0, wins: 0, kills: 0, deaths: 0 } };
    saveUsers(); send(ws, { type: 'registered' }); return;
  }
  if (msg.type === 'login') {
    const username = typeof msg.username === 'string' ? msg.username.trim() : '';
    const user = users[username];
    if (!user || typeof msg.password !== 'string' || !(await passwordMatches(msg.password, user))) return error(ws, 'Неверное имя или пароль.');
    const token = randomToken(); sessions.set(token, username);
    const c = clients.get(ws); c.username = username; c.token = token;
    send(ws, { type: 'auth_ok', token, user: safeUser(username) }); return;
  }
  if (msg.type === 'ping') return send(ws, { type: 'pong', now: Date.now() });
  const username = getAuth(ws, msg); if (!username) return;
  if (msg.type === 'create_room') return createRoom(ws, msg.maxPlayers, msg.mode);
  if (msg.type === 'join_room') {
    const code = typeof msg.code === 'string' ? msg.code.trim().toUpperCase() : '';
    const room = rooms.get(code); if (!room) return error(ws, 'Комната не найдена. Проверь код.');
    return enterRoom(ws, room);
  }
  if (msg.type === 'leave_room') return leaveRoom(ws);
  if (msg.type === 'quick_match') {
    leaveRoom(ws);
    const mode = msg.mode === 'hostage' ? 'hostage' : 'bomb';
    const available = [...rooms.values()].find(r => r.mode === mode && r.players.length < r.maxPlayers);
    if (available) { enterRoom(ws, available); send(ws, { type: 'match_found', room: roomSnapshot(available) }); }
    else { createRoom(ws, 10, mode); const c = clients.get(ws); const room = rooms.get(c.roomCode); send(ws, { type: 'match_found', room: roomSnapshot(room) }); }
    return;
  }
  if (msg.type === 'get_stats') return sendStats(ws, username);
  // Reserve a server-validated event interface for the next stage. Never trust client-reported stats.
  if (msg.type === 'report_match_result') return error(ws, 'Результаты матча будут учитываться после подключения авторитетной игровой симуляции.');
  return error(ws, 'Неизвестная команда.');
}
const server = http.createServer((req, res) => {
  const pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname);
  const requested = pathname === '/' ? '/index.html' : pathname;
  const file = path.resolve(ROOT, '.' + requested);
  if (!file.startsWith(ROOT + path.sep) && file !== path.join(ROOT, 'index.html')) { res.writeHead(403); return res.end('Forbidden'); }
  fs.readFile(file, (err, data) => {
    if (err) { res.writeHead(404); return res.end('Not found'); }
    const ext = path.extname(file);
    const types = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8', '.json': 'application/json; charset=utf-8' };
    res.writeHead(200, { 'Content-Type': types[ext] || 'application/octet-stream', 'X-Content-Type-Options': 'nosniff', 'Cache-Control': 'no-store' }); res.end(data);
  });
});
const wss = new WebSocketServer({ server, maxPayload: MAX_MESSAGE });
wss.on('connection', ws => {
  clients.set(ws, { username: null, roomCode: null, token: null });
  send(ws, { type: 'info', message: 'Соединение с сервером установлено.' });
  ws.on('message', async raw => {
    try { const msg = JSON.parse(raw.toString()); await handle(ws, msg); }
    catch (e) { console.error('Message handler error:', e.message); error(ws, 'Внутренняя ошибка сервера.'); }
  });
  ws.on('close', () => { leaveRoom(ws); const c = clients.get(ws); if (c?.token) sessions.delete(c.token); clients.delete(ws); });
});
server.listen(PORT, HOST, () => console.log(`CS2 Bomb Mode Arena stage 1: http://${HOST}:${PORT}`));
