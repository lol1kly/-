'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = Number(process.env.PORT || 3000);
const HOST = process.env.HOST || '0.0.0.0';
const ROOT = __dirname;
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
// Server-owned weapon parameters. Client-reported damage, target and headshot are never trusted.
const WEAPONS = {
  rifle: { damage: 36, head: 4, rate: 100, range: 100, radius: 0.72 },
  sniper: { damage: 110, head: 4, rate: 1200, range: 150, radius: 0.58 },
  pistol: { damage: 28, head: 3.5, rate: 200, range: 80, radius: 0.72 },
  smg: { damage: 22, head: 3, rate: 70, range: 60, radius: 0.78 },
  knife: { damage: 150, head: 1, rate: 500, range: 2.8, radius: 1.0 }
};
const MAX_SPEED = 12; // game units/second; client movement is bounded by server validation
const BOMB_FUSE_MS = 40000;
const PLANT_MS = 2500;
const DEFUSE_MS = 5000;
const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));
const distance2 = (a,b) => Math.hypot(a.x-b.x, a.z-b.z);
function teamFor(room, name) { return room.teams[name] || 'red'; }
function broadcast(room, packet) { for (const [ws,c] of clients) if (c.roomCode === room.code) send(ws, packet); }
function resetPlayer(room, name) { room.health[name] = 100; room.ammo[name] = { rifle:30, sniper:10, pistol:12, smg:35, knife:1 }; room.lastShot[name] = 0; }
function finishRound(room, winner, reason) {
  if (room.gameState.bombPhase === 'ended') return;
  room.gameState.bombPhase = 'ended'; room.gameState.winner = winner; room.gameState.endReason = reason;
  room.gameState.bomb = room.gameState.bomb || null;
  room.gameState.score[winner] = (room.gameState.score[winner] || 0) + 1;
  room.gameState.roundEndsAt = Date.now() + 5000;
  broadcastGameState(room);
}
function tickRooms() {
  const now = Date.now();
  for (const room of rooms.values()) {
    const g = room.gameState;
    if (g.bombPhase === 'planted' && g.bomb && now >= g.bomb.explodesAt) finishRound(room, 'red', 'exploded');
    if (g.bombPhase === 'ended' && g.roundEndsAt && now >= g.roundEndsAt) {
      g.round += 1; g.bombPhase = 'live'; g.bomb = null; g.winner = null; g.endReason = null; g.roundEndsAt = null; g.actions = {};
      for (const name of room.players) resetPlayer(room, name);
      broadcastGameState(room); broadcastPositions(room);
    }
  }
}
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
  return { code: room.code, mode: room.mode, maxPlayers: room.maxPlayers, players: [...room.players].map((name, index) => ({ username: name, team: room.teams[name] || (index % 2 === 0 ? 'red' : 'blue'), online: [...clients.entries()].some(([ws,c]) => ws.readyState === WebSocket.OPEN && c.username === name && c.roomCode === room.code) })) };
}
function broadcastGameState(room) { for (const [ws,c] of clients) if (c.roomCode === room.code) send(ws, { type: 'game_state', state: room.gameState }); }
function broadcastRoom(room) { const state = { type: 'room_state', room: roomSnapshot(room) }; for (const [ws,c] of clients) if (c.roomCode === room.code) send(ws, state); }
function startMatchIfReady(room) { if (!room || room.started || room.players.length < 2) return; room.started=true; room.mode='bomb'; room.gameState.bombPhase='live'; const packet={type:'match_started',room:roomSnapshot(room),mode:'bomb',startedAt:Date.now()}; for(const [ws,c] of clients) if(c.roomCode===room.code) send(ws,packet); }
function broadcastPositions(room) { const state = { type: 'player_states', players: Object.entries(room.positions).map(([username,p]) => ({ username, ...p, team: teamFor(room, username), hp: room.health[username] ?? 100 })) }; for (const [ws,c] of clients) if (c.roomCode === room.code) send(ws, state); }
function leaveRoom(ws) {
  const c = clients.get(ws); if (!c || !c.roomCode) return;
  const room = rooms.get(c.roomCode); c.roomCode = null;
  if (room) {
    const wasStarted = !!room.started;
    room.players = room.players.filter(n => n !== c.username);
    if (c.username) { delete room.positions[c.username]; delete room.realPositions[c.username]; delete room.health[c.username]; delete room.ammo[c.username]; delete room.lastShot[c.username]; delete room.lastGrenade[c.username]; delete room.teams[c.username]; }
    if (!room.players.length) rooms.delete(room.code);
    else {
      // Leaving is not a win condition. Freeze the current match without awarding a round or match win.
      if (wasStarted) { room.started = false; broadcast(room, { type: 'opponent_left', username: c.username, winner: null, awardWin: false }); }
      broadcastRoom(room); broadcastPositions(room);
    }
  }
  send(ws, { type: 'room_left' });
}
function enterRoom(ws, room) {
  const c = clients.get(ws); if (!c || !c.username) return error(ws, 'Сначала войди в аккаунт.');
  leaveRoom(ws);
  if (room.players.length >= room.maxPlayers) return error(ws, 'Комната заполнена.');
  if (!room.players.includes(c.username)) room.players.push(c.username);
  c.roomCode = room.code;
  if (!room.teams[c.username]) { const redCount=room.players.filter(n=>room.teams[n]==='red').length, blueCount=room.players.filter(n=>room.teams[n]==='blue').length; room.teams[c.username]=redCount===blueCount?(Math.random()<0.5?'red':'blue'):(redCount<blueCount?'red':'blue'); }
  if (room.health[c.username] === undefined) resetPlayer(room, c.username);
  // Seed the authoritative snapshot at the same team spawn used by the browser. This makes
  // the opponent visible immediately, even before the first movement packet arrives.
  if (!room.positions[c.username]) room.positions[c.username] = { x: 0, y: 0, z: teamFor(room,c.username)==='red' ? 62 : -62, yaw: teamFor(room,c.username)==='red' ? 0 : Math.PI, pitch: 0, hp: room.health[c.username] ?? 100, at: Date.now() };
  broadcastRoom(room);
  send(ws, { type: 'game_state', state: room.gameState });
  startMatchIfReady(room);
  broadcastPositions(room);
}
function createRoom(ws, maxPlayers = 2, mode = 'bomb') {
  const c = clients.get(ws); if (!c || !c.username) return error(ws, 'Сначала войди в аккаунт.');
  leaveRoom(ws);
  let code; do { code = randomCode(); } while (rooms.has(code));
  const room = { code, mode: 'bomb', maxPlayers: 2, players: [], positions: Object.create(null), realPositions: Object.create(null), health: Object.create(null), ammo: Object.create(null), lastShot: Object.create(null), lastGrenade: Object.create(null), grenades: [], teams: Object.create(null), gameState: { bombPhase: 'live', bomb: null, round: 1, score: { red: 0, blue: 0 }, actions: {} } };
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
  if (msg.type === 'create_room') return createRoom(ws, 2, 'bomb');
  if (msg.type === 'join_room') {
    const code = typeof msg.code === 'string' ? msg.code.trim().toUpperCase() : '';
    const room = rooms.get(code); if (!room) return error(ws, 'Комната не найдена. Проверь код.');
    return enterRoom(ws, room);
  }
  if (msg.type === 'leave_room') return leaveRoom(ws);
  if (msg.type === 'player_state') {
    const c = clients.get(ws), room = c?.roomCode && rooms.get(c.roomCode);
    if (!room || !room.players.includes(username)) return error(ws, 'Сначала войди в комнату.');
    const p = msg.position || {}, nums = ['x','y','z','yaw','pitch'];
    if (!nums.every(k => Number.isFinite(p[k])) || Math.abs(p.x)>100 || Math.abs(p.z)>100 || Math.abs(p.y)>20 || Math.abs(p.yaw)>100 || Math.abs(p.pitch)>4) return;
    const now = Date.now(), prev = room.positions[username];
    if (prev && room.realPositions[username]) {
      const dt = clamp((now - (prev.at || now))/1000, 0.02, 0.25);
      const maxTravel = MAX_SPEED * dt + 1.2; // allowance for packet jitter and jumps
      const d = Math.hypot(p.x-prev.x, p.y-prev.y, p.z-prev.z);
      if (d > maxTravel) return; // reject teleport/speed-hack update
    }
    room.positions[username] = { x:p.x, y:p.y, z:p.z, yaw:p.yaw, pitch:p.pitch, hp:room.health[username] ?? 100, at:now };
    room.realPositions[username] = true;
    broadcastPositions(room); return;
  }
  if (msg.type === 'player_shot') {
    const c = clients.get(ws), room = c?.roomCode && rooms.get(c.roomCode);
    if (!room || !room.players.includes(username)) return error(ws, 'Сначала войди в комнату.');
    const shooter = room.positions[username];
    if (!shooter || (room.health[username] ?? 100) <= 0) return;
    const weaponKey = typeof msg.weaponIcon === 'string' && WEAPONS[msg.weaponIcon] ? msg.weaponIcon : 'rifle';
    const weapon = WEAPONS[weaponKey], now = Date.now();
    if (now - (room.lastShot[username] || 0) < weapon.rate * 0.9) return;
    room.lastShot[username] = now;
    room.ammo[username] ||= { rifle:30, sniper:10, pistol:12, smg:35, knife:1 };
    if ((room.ammo[username][weaponKey] ?? 0) <= 0) { send(ws,{type:'shot_ack',hit:false,empty:true,ammo:0}); return; }
    room.ammo[username][weaponKey] -= 1;
    const yaw = Number(msg.yaw), pitch = Number(msg.pitch);
    if (!Number.isFinite(yaw) || !Number.isFinite(pitch) || Math.abs(pitch) > 1.7) return;
    const cp = Math.cos(pitch), dir = { x:-Math.sin(yaw)*cp, y:Math.sin(pitch), z:-Math.cos(yaw)*cp };
    let best = null;
    for (const target of room.players) {
      if (target === username || teamFor(room,target) === teamFor(room,username) || (room.health[target] ?? 100) <= 0) continue;
      const v = room.positions[target]; if (!v) continue;
      // Evaluate head and torso as server-side hit volumes, not client-provided target/damage.
      for (const part of [{x:v.x,y:(v.y||0)+1.55,z:v.z,head:true,r:weapon.radius*0.62},{x:v.x,y:(v.y||0)+0.75,z:v.z,head:false,r:weapon.radius}]) {
        const ox=part.x-(shooter.x), oy=part.y-((shooter.y||0)+1.5), oz=part.z-shooter.z;
        const along=ox*dir.x+oy*dir.y+oz*dir.z;
        if (along < 0 || along > weapon.range) continue;
        const px=ox-dir.x*along, py=oy-dir.y*along, pz=oz-dir.z*along;
        const miss=Math.hypot(px,py,pz);
        if (miss <= part.r && (!best || along < best.along)) best={target,along,head:part.head};
      }
    }
    if (!best) { send(ws,{type:'shot_ack',hit:false,ammo:room.ammo[username]?.[weaponKey]}); return; }
    const damage = Math.min(1000, weapon.damage * (best.head ? weapon.head : 1));
    room.health[best.target] = Math.max(0,(room.health[best.target] ?? 100)-damage);
    if (room.positions[best.target]) room.positions[best.target].hp=room.health[best.target];
    const event={type:'player_hit',killer:username,target:best.target,victim:best.target,hp:room.health[best.target],damage,headshot:best.head,weapon:weaponKey,serverAuthoritative:true};
    broadcast(room,event); broadcastPositions(room);
    if (room.health[best.target] <= 0) {
      room.gameState.lastKill={killer:username,victim:best.target,at:now};
      const aliveRed=room.players.some(n=>teamFor(room,n)==='red' && (room.health[n]??100)>0);
      const aliveBlue=room.players.some(n=>teamFor(room,n)==='blue' && (room.health[n]??100)>0);
      if (!aliveRed || !aliveBlue) finishRound(room, aliveRed?'red':'blue','elimination');
    }
    return;
  }
  if (msg.type === 'game_event') {
    const c = clients.get(ws), room = c?.roomCode && rooms.get(c.roomCode);
    if (!room || !room.players.includes(username)) return error(ws, 'Сначала войди в комнату.');
    const event = msg.event, pos = room.positions[username], team=teamFor(room,username), g=room.gameState, now=Date.now();
    if (event === 'bomb_plant_start') {
      if (g.bombPhase !== 'live' || team !== 'red' || !pos || ![[-32,-8],[32,-8]].some(([sx,sz])=>Math.hypot(pos.x-sx,pos.z-sz)<7)) return error(ws,'Нельзя начать установку здесь.');
      g.actions[username]={type:'plant',startedAt:now,x:pos.x,z:pos.z}; broadcastGameState(room); return;
    } else if (event === 'bomb_defuse_start') {
      if (g.bombPhase !== 'planted' || team !== 'blue' || !pos || !g.bomb || distance2(pos,g.bomb)>4.5) return error(ws,'Нельзя начать обезвреживание здесь.');
      g.actions[username]={type:'defuse',startedAt:now}; broadcastGameState(room); return;
    } else if (event === 'bomb_planted') {
      const action=g.actions[username];
      if (g.bombPhase !== 'live' || team !== 'red' || !pos || !action || action.type!=='plant' || now-action.startedAt<PLANT_MS-250) return error(ws,'Сервер не подтвердил время установки.');
      const x=Number(msg.x), z=Number(msg.z);
      if (!Number.isFinite(x)||!Number.isFinite(z)||Math.hypot(pos.x-x,pos.z-z)>2.5 || Math.hypot(pos.x-action.x,pos.z-action.z)>3) return error(ws,'Позиция установки не совпадает с серверной.');
      const nearSite=[[-32,-8],[32,-8]].some(([sx,sz])=>Math.hypot(pos.x-sx,pos.z-sz)<7);
      if (!nearSite) return error(ws,'Устанавливать бомбу можно только на точке A или B.');
      delete g.actions[username]; g.bombPhase='planted'; g.bomb={x:pos.x,z:pos.z,plantedAt:now,explodesAt:now+BOMB_FUSE_MS,planter:username};
    } else if (event === 'bomb_defused') {
      const action=g.actions[username];
      if (g.bombPhase!=='planted'||team!=='blue'||!pos||!g.bomb||distance2(pos,g.bomb)>4.5 || !action || action.type!=='defuse' || now-action.startedAt<DEFUSE_MS-250) return error(ws,'Сервер не подтвердил время обезвреживания.');
      delete g.actions[username]; finishRound(room,'blue','defused'); return;
    } else if (event === 'bomb_exploded') {
      // Clients cannot declare an explosion; the server timer is authoritative.
      return error(ws,'Взрыв рассчитывается сервером.');
    } else if (event === 'round_start') {
      if (team !== 'red' || g.bombPhase !== 'idle') return error(ws,'Раундом управляет сервер.');
      g.bombPhase='live'; g.bomb=null; g.winner=null; g.endReason=null;
    } else return error(ws,'Неизвестное игровое событие.');
    broadcastGameState(room); return;
  }
  if (msg.type === 'grenade_throw') {
    const c=clients.get(ws), room=c?.roomCode && rooms.get(c.roomCode), pos=room?.positions[username];
    if(!room||!pos) return error(ws,'Сначала войди в комнату.');
    const type=['flash','he','molotov','smoke'].includes(msg.grenadeType)?msg.grenadeType:null;
    if(!type) return error(ws,'Неизвестный тип гранаты.');
    const now=Date.now(), last=room.lastGrenade[username]||0;
    if(now-last<700) return error(ws,'Слишком быстрое использование гранат.');
    room.lastGrenade[username]=now;
    const yaw=Number(msg.yaw),pitch=Number(msg.pitch); if(!Number.isFinite(yaw)||!Number.isFinite(pitch)) return;
    const dir={x:-Math.sin(yaw)*Math.cos(pitch),y:Math.sin(pitch),z:-Math.cos(yaw)*Math.cos(pitch)};
    const grenade={id:crypto.randomBytes(6).toString('hex'),owner:username,team:teamFor(room,username),type,x:pos.x,y:(pos.y||0)+1.3,z:pos.z,vx:dir.x*8,vy:dir.y*8+3,vz:dir.z*8,born:now,fuse:type==='he'?2500:type==='flash'?1800:2500};
    room.grenades.push(grenade); broadcast(room,{type:'grenade_spawn',grenade}); return;
  }

  if (msg.type === 'quick_match') {
    leaveRoom(ws);
    // This build intentionally exposes only Bomb mode and 1v1 matchmaking.
    const available = [...rooms.values()].find(r => r.mode === 'bomb' && !r.started && r.players.length === 1 && r.players[0] !== username);
    if (available) {
      enterRoom(ws, available);
      send(ws, { type: 'match_found', room: roomSnapshot(available) });
      startMatchIfReady(available);
    } else {
      createRoom(ws, 2, 'bomb');
      const c = clients.get(ws), room = rooms.get(c.roomCode);
      send(ws, { type: 'match_found', room: roomSnapshot(room) });
    }
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
wss.on('connection', (ws, req) => {
  console.log('[ws] connected', req.socket.remoteAddress);
  clients.set(ws, { username: null, roomCode: null, token: null });
  send(ws, { type: 'info', message: 'Соединение с сервером установлено.' });
  ws.on('message', async raw => {
    try { const msg = JSON.parse(raw.toString()); await handle(ws, msg); }
    catch (e) { console.error('Message handler error:', e.message); error(ws, 'Внутренняя ошибка сервера.'); }
  });
  ws.on('close', (code, reason) => { const c = clients.get(ws); console.log('[ws] closed', c?.username || 'anonymous', code, reason?.toString() || ''); leaveRoom(ws); if (c?.token) sessions.delete(c.token); clients.delete(ws); });
});
// Keep sending snapshots while a match is active. This recovers clients that received the
// first snapshot before their Three.js scene was ready and provides a steady state stream.
setInterval(() => {
  for (const room of rooms.values()) {
    if (room.started && room.players.length >= 2) broadcastPositions(room);
  }
}, 100).unref();
setInterval(tickRooms, 100).unref();
server.listen(PORT, HOST, () => console.log(`CS2 Bomb Mode Arena v30 multiplayer diagnostics: http://${HOST}:${PORT}`));
