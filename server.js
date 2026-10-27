'use strict';
// CS2 Bomb Mode Arena — online server v35
// Server-authoritative: movement + map collisions, hitscan with wall occlusion, grenades,
// bomb logic, rounds, match end and account statistics. Clients send only intent.
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = Number(process.env.PORT || 3000);
const HOST = process.env.HOST || '0.0.0.0';
const ROOT = __dirname;
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
const DB_FILE = path.join(DATA_DIR, 'users.json');
const MAX_MESSAGE = 16 * 1024;

// ---------------------------------------------------------------- accounts
fs.mkdirSync(DATA_DIR, { recursive: true });
const users = Object.create(null);
try { Object.assign(users, JSON.parse(fs.readFileSync(DB_FILE, 'utf8'))); } catch { /* first start */ }
function saveUsers() {
  try {
    const tmp = DB_FILE + '.tmp';
    fs.writeFileSync(tmp, JSON.stringify(users, null, 2));
    fs.renameSync(tmp, DB_FILE);
  } catch (e) { console.error('[db] save failed:', e.message); }
}
const SESSION_TTL_MS = 24 * 3600 * 1000;
const sessions = new Map();   // token -> { username, expires }; survives socket reconnects
const clients = new Map();    // ws -> { username, roomCode, token, ip, ... }
const rooms = new Map();
const authAttempts = new Map(); // ip -> { n, reset }
const AUTH_LIMIT_PER_MIN = Number(process.env.AUTH_LIMIT_PER_MIN || 12);

// ---------------------------------------------------------------- game constants
const WEAPONS = {
  rifle:  { damage: 36,  head: 4,   rate: 100,  range: 100 },
  sniper: { damage: 110, head: 4,   rate: 1200, range: 150 },
  pistol: { damage: 28,  head: 3.5, rate: 200,  range: 80 },
  smg:    { damage: 22,  head: 3,   rate: 70,   range: 60 },
  knife:  { damage: 150, head: 1,   rate: 500,  range: 2.8 }
};
const WALK_SPEED = 6.5, SCOPED_SPEED = 3;
const GRAVITY = 22, JUMP_SPEED = 7.5;
const PLAYER_RADIUS = 0.4, EYE_HEIGHT = 1.7;
const TICK_MS = 33;
const FREEZE_MS = Number(process.env.FREEZE_MS || 5000), LIVE_MS = 110000, ROUND_END_MS = Number(process.env.ROUND_END_MS || 5000);
const BOMB_FUSE_MS = 40000, PLANT_MS = 2500, DEFUSE_MS = 5000;
const WIN_ROUNDS = Number(process.env.WIN_ROUNDS || 7);
const DISCONNECT_GRACE_MS = 15000;
const INPUT_STALE_MS = 500;
const MAX_GRENADES_PER_ROUND = 4;
const GRENADE_FUSE = { flash: 1100, he: 1500, molotov: 1200, smoke: 1500 };
const BOMB_SITES = [[-32, -8], [32, -8]];

const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));
const distance2 = (a, b) => Math.hypot(a.x - b.x, a.z - b.z);

// ---------------------------------------------------------------- map (must match buildArenaMap() in index.html, dust2 bomb mode)
function box(cx, cy, cz, sx, sy, sz) {
  return { minX: cx - sx / 2, maxX: cx + sx / 2, minY: cy - sy / 2, maxY: cy + sy / 2, minZ: cz - sz / 2, maxZ: cz + sz / 2 };
}
const CRATES = [
  [-8, 1.5, -12], [-5, 1.5, -12], [-8, 4.5, -12], [12, 1.5, -15], [15, 1.5, -10], [-15, 1.5, 10],
  [0, 1.5, -25], [10, 1.5, 5], [-12, 1.5, -2],
  [-34, 1.5, -30], [-28, 1.5, -42], [34, 1.5, -30], [28, 1.5, -48],
  [-35, 1.5, 30], [-28, 1.5, 42], [35, 1.5, 30], [28, 1.5, 48],
  [-15, 1.5, -35], [15, 1.5, 35], [20, 1.5, -50], [-20, 1.5, 50],
  [0, 1.5, 25], [0, 1.5, -45]
];
const COLLIDERS = [
  box(0, 6, -80, 160, 12, 2), box(0, 6, 80, 160, 12, 2), box(80, 6, 0, 2, 12, 160), box(-80, 6, 0, 2, 12, 160),
  ...[[-24, 4, -20], [24, 4, -20], [-24, 4, 20], [24, 4, 20]].map(p => box(p[0], p[1], p[2], 20, 8, 2)),
  ...CRATES.map(p => box(p[0], p[1], p[2], 3, 3, 3))
];
function playerCollides(x, z, feetY) {
  for (const b of COLLIDERS) {
    if (feetY >= b.maxY - 0.05) continue;
    if (x + PLAYER_RADIUS > b.minX && x - PLAYER_RADIUS < b.maxX && z + PLAYER_RADIUS > b.minZ && z - PLAYER_RADIUS < b.maxZ) return true;
  }
  return false;
}
function pointInSolid(x, y, z) {
  for (const b of COLLIDERS) if (x > b.minX && x < b.maxX && y > b.minY && y < b.maxY && z > b.minZ && z < b.maxZ) return true;
  return false;
}
function rayBoxT(ox, oy, oz, dx, dy, dz, b, maxT) {
  let tmin = 0, tmax = maxT;
  const o = [ox, oy, oz], d = [dx, dy, dz], lo = [b.minX, b.minY, b.minZ], hi = [b.maxX, b.maxY, b.maxZ];
  for (let i = 0; i < 3; i++) {
    if (Math.abs(d[i]) < 1e-9) { if (o[i] < lo[i] || o[i] > hi[i]) return Infinity; }
    else {
      let t1 = (lo[i] - o[i]) / d[i], t2 = (hi[i] - o[i]) / d[i];
      if (t1 > t2) { const t = t1; t1 = t2; t2 = t; }
      if (t1 > tmin) tmin = t1;
      if (t2 < tmax) tmax = t2;
      if (tmin > tmax) return Infinity;
    }
  }
  return tmin;
}
function wallDistance(ox, oy, oz, dx, dy, dz, maxT) {
  let best = Infinity;
  for (const b of COLLIDERS) { const t = rayBoxT(ox, oy, oz, dx, dy, dz, b, maxT); if (t < best) best = t; }
  return best;
}
function segmentClear(a, b) {
  const dx = b.x - a.x, dy = b.y - a.y, dz = b.z - a.z, len = Math.hypot(dx, dy, dz);
  if (len < 1e-6) return true;
  return wallDistance(a.x, a.y, a.z, dx / len, dy / len, dz / len, len) >= len - 0.05;
}

// ---------------------------------------------------------------- helpers
const send = (ws, data) => { if (ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify(data)); };
const error = (ws, message) => send(ws, { type: 'error', message });
const randomToken = () => crypto.randomBytes(32).toString('hex');
const randomCode = () => crypto.randomBytes(3).toString('hex').toUpperCase();
const safeUser = name => users[name] ? ({ username: name, stats: users[name].stats }) : null;
const validName = name => typeof name === 'string' && /^[a-zA-Z0-9_ -]{3,20}$/.test(name.trim());
function hashPassword(password, salt = crypto.randomBytes(16).toString('hex')) {
  return new Promise((resolve, reject) => crypto.scrypt(password, salt, 64, (err, key) => err ? reject(err) : resolve({ salt, hash: key.toString('hex') })));
}
async function passwordMatches(password, record) {
  if (!record || typeof record.salt !== 'string' || typeof record.hash !== 'string') return false;
  const got = await hashPassword(password, record.salt);
  const a = Buffer.from(got.hash, 'hex'), b = Buffer.from(record.hash, 'hex');
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}
function authThrottled(ip) {
  const now = Date.now();
  let e = authAttempts.get(ip);
  if (!e || now > e.reset) { e = { n: 0, reset: now + 60000 }; authAttempts.set(ip, e); }
  return ++e.n > AUTH_LIMIT_PER_MIN;
}
const teamFor = (room, name) => room.teams[name] || 'red';
const isAlive = (room, name) => (room.health[name] ?? 100) > 0;
function broadcast(room, packet) { for (const [ws, c] of clients) if (c.roomCode === room.code) send(ws, packet); }
function publicState(room) { return { ...room.gameState, serverNow: Date.now() }; }
function broadcastGameState(room) { broadcast(room, { type: 'game_state', state: publicState(room) }); }
function roomSnapshot(room) {
  return {
    code: room.code, mode: room.mode, maxPlayers: room.maxPlayers,
    players: room.players.map((name, index) => ({
      username: name, team: room.teams[name] || (index % 2 === 0 ? 'red' : 'blue'),
      online: [...clients.values()].some(c => c.username === name && c.roomCode === room.code)
    }))
  };
}
function broadcastRoom(room) { broadcast(room, { type: 'room_state', room: roomSnapshot(room) }); }
function positionsPacket(room) {
  return {
    type: 'player_states', serverNow: Date.now(),
    players: room.players.filter(n => room.positions[n]).map(n => {
      const p = room.positions[n];
      return { username: n, x: p.x, y: p.y, z: p.z, yaw: p.yaw, pitch: p.pitch, team: teamFor(room, n), hp: room.health[n] ?? 100 };
    })
  };
}
function broadcastPositions(room) { broadcast(room, positionsPacket(room)); }
const spawnFor = (room, name) => {
  const red = teamFor(room, name) === 'red';
  return { x: 0, y: 0, z: red ? 30 : -30, yaw: red ? 0 : Math.PI, pitch: 0, vy: 0, onGround: true, simAt: Date.now() };
};
function resetPlayer(room, name) { room.health[name] = 100; room.lastShot[name] = 0; room.lastGrenade[name] = 0; room.grenadesThrown[name] = 0; }

// ---------------------------------------------------------------- stats
function commitStats(room, completed, winnerTeam) {
  if (room.statsCommitted) return;
  room.statsCommitted = true;
  for (const [name, s] of Object.entries(room.stats)) {
    const u = users[name]; if (!u) continue;
    u.stats = u.stats || { matches: 0, wins: 0, kills: 0, deaths: 0 };
    u.stats.kills += s.kills; u.stats.deaths += s.deaths;
    if (completed) { u.stats.matches += 1; if (room.teams[name] === winnerTeam) u.stats.wins += 1; }
  }
  saveUsers();
  for (const [ws, c] of clients) if (c.username && room.stats[c.username] && users[c.username]) send(ws, { type: 'stats', stats: users[c.username].stats });
}

// ---------------------------------------------------------------- rounds & match
function startRound(room) {
  const g = room.gameState, now = Date.now();
  g.bombPhase = 'freeze'; g.freezeEndsAt = now + FREEZE_MS; g.liveEndsAt = g.freezeEndsAt + LIVE_MS;
  g.bomb = null; g.winner = null; g.endReason = null; g.roundEndsAt = null; g.actions = {};
  room.grenades = []; room.fires = [];
  for (const name of room.players) {
    resetPlayer(room, name);
    room.positions[name] = spawnFor(room, name);
    delete room.inputs[name];
  }
  broadcastGameState(room); broadcastPositions(room);
}
function finishRound(room, winner, reason) {
  const g = room.gameState;
  if (g.bombPhase === 'ended' || room.over) return;
  g.bombPhase = 'ended'; g.winner = winner; g.endReason = reason;
  g.score[winner] = (g.score[winner] || 0) + 1;
  g.roundEndsAt = Date.now() + ROUND_END_MS;
  room.grenades = []; room.fires = [];
  broadcastGameState(room);
}
function finishMatch(room) {
  const g = room.gameState;
  const winnerTeam = g.score.red > g.score.blue ? 'red' : 'blue';
  const winner = room.players.find(n => room.teams[n] === winnerTeam) || null;
  room.over = true; room.started = false; room.closed = true;
  commitStats(room, true, winnerTeam);
  broadcast(room, { type: 'match_over', winnerTeam, winner, score: g.score });
}
function checkElimination(room) {
  const g = room.gameState;
  if (g.bombPhase !== 'live' && g.bombPhase !== 'planted') return;
  const aliveRed = room.players.some(n => teamFor(room, n) === 'red' && isAlive(room, n));
  const aliveBlue = room.players.some(n => teamFor(room, n) === 'blue' && isAlive(room, n));
  if (!aliveBlue) finishRound(room, 'red', 'elimination');
  else if (!aliveRed && g.bombPhase !== 'planted') finishRound(room, 'blue', 'elimination');
}
function applyDamage(room, killer, target, damage, weapon, headshot) {
  if (!isAlive(room, target)) return;
  damage = Math.round(damage);
  room.health[target] = Math.max(0, (room.health[target] ?? 100) - damage);
  const hp = room.health[target];
  broadcast(room, { type: 'player_hit', killer, target, victim: target, hp, damage, headshot: !!headshot, weapon, serverAuthoritative: true });
  broadcastPositions(room);
  if (hp <= 0) {
    if (room.stats[killer]) room.stats[killer].kills += 1;
    if (room.stats[target]) room.stats[target].deaths += 1;
    room.gameState.lastKill = { killer, victim: target, at: Date.now() };
    checkElimination(room);
  }
}

// ---------------------------------------------------------------- simulation
function explodeGrenade(room, g, now) {
  broadcast(room, { type: 'grenade_explode', id: g.id, gtype: g.type, x: g.x, y: g.y, z: g.z, owner: g.owner, team: g.team });
  if (g.type === 'he') {
    for (const target of room.players) {
      if (target === g.owner || teamFor(room, target) === g.team || !isAlive(room, target)) continue;
      const p = room.positions[target]; if (!p) continue;
      const chest = { x: p.x, y: p.y + 1.0, z: p.z };
      const d = Math.hypot(chest.x - g.x, chest.y - g.y, chest.z - g.z);
      if (d < 7 && segmentClear({ x: g.x, y: g.y + 0.3, z: g.z }, chest)) applyDamage(room, g.owner, target, 90 * (1 - d / 8), 'he', false);
    }
  } else if (g.type === 'molotov') {
    room.fires.push({ x: g.x, z: g.z, until: now + 7000, last: 0, owner: g.owner, team: g.team });
  }
}
function tickGrenades(room, now, dt) {
  for (let i = room.grenades.length - 1; i >= 0; i--) {
    const g = room.grenades[i];
    if (now - g.born >= g.fuse) { room.grenades.splice(i, 1); explodeGrenade(room, g, now); continue; }
    g.vy -= 27 * dt;
    const nx = g.x + g.vx * dt; if (pointInSolid(nx, g.y, g.z)) g.vx *= -0.4; else g.x = nx;
    const nz = g.z + g.vz * dt; if (pointInSolid(g.x, g.y, nz)) g.vz *= -0.4; else g.z = nz;
    const ny = g.y + g.vy * dt; if (pointInSolid(g.x, ny, g.z)) g.vy *= -0.35; else g.y = ny;
    if (g.y < 0.25) {
      g.y = 0.25; g.vy = Math.abs(g.vy) * 0.35; if (g.vy < 1.5) g.vy = 0;
      const f = Math.pow(0.72, dt * 60); g.vx *= f; g.vz *= f;
    }
    g.x = clamp(g.x, -78, 78); g.z = clamp(g.z, -78, 78);
  }
  for (let i = room.fires.length - 1; i >= 0; i--) {
    const f = room.fires[i];
    if (now >= f.until) { room.fires.splice(i, 1); continue; }
    if (now - f.last < 500) continue;
    f.last = now;
    for (const target of room.players) {
      if (target === f.owner || teamFor(room, target) === f.team || !isAlive(room, target)) continue;
      const p = room.positions[target];
      if (p && Math.hypot(p.x - f.x, p.z - f.z) < 3.3 && p.y < 1.5) applyDamage(room, f.owner, target, 12, 'molotov', false);
    }
  }
}
function tickPlayers(room, now) {
  const frozen = room.gameState.bombPhase === 'freeze';
  for (const name of room.players) {
    const pos = room.positions[name]; if (!pos) continue;
    const dt = clamp((now - (pos.simAt || now)) / 1000, 0, 0.1);
    pos.simAt = now;
    if (!isAlive(room, name)) continue;
    const input = room.inputs[name]; if (!input) continue;
    pos.yaw = input.yaw; pos.pitch = input.pitch;
    if (frozen) { pos.vy = 0; pos.y = 0; continue; }
    const fresh = now - input.at < INPUT_STALE_MS; // a silent client must not keep running
    pos.onGround = pos.y <= 0.0001;
    if (fresh && input.jumpAt && now - input.jumpAt < 200 && pos.onGround) { pos.vy = JUMP_SPEED; pos.onGround = false; input.jumpAt = 0; }
    pos.vy -= GRAVITY * dt; pos.y += pos.vy * dt;
    if (pos.y <= 0) { pos.y = 0; pos.vy = 0; pos.onGround = true; }
    if (!fresh) continue;
    let forward = (input.forward ? 1 : 0) - (input.backward ? 1 : 0);
    let strafe = (input.right ? 1 : 0) - (input.left ? 1 : 0);
    const len = Math.hypot(forward, strafe); if (!len) continue;
    forward /= len; strafe /= len;
    const speed = (input.scoped ? SCOPED_SPEED : WALK_SPEED) * dt;
    const dx = (-Math.sin(pos.yaw) * forward + Math.cos(pos.yaw) * strafe) * speed;
    const dz = (-Math.cos(pos.yaw) * forward - Math.sin(pos.yaw) * strafe) * speed;
    const nx = clamp(pos.x + dx, -76, 76); if (!playerCollides(nx, pos.z, pos.y)) pos.x = nx;
    const nz = clamp(pos.z + dz, -76, 76); if (!playerCollides(pos.x, nz, pos.y)) pos.z = nz;
  }
}
function tick() {
  const now = Date.now();
  for (const room of rooms.values()) {
    if (!room.started || room.over) continue;
    const g = room.gameState;
    if (g.bombPhase === 'freeze' && now >= g.freezeEndsAt) { g.bombPhase = 'live'; broadcastGameState(room); }
    tickPlayers(room, now);
    tickGrenades(room, now, TICK_MS / 1000);
    if (g.bombPhase === 'live' && now >= g.liveEndsAt) finishRound(room, 'blue', 'time_expired');
    if (g.bombPhase === 'planted' && g.bomb && now >= g.bomb.explodesAt) finishRound(room, 'red', 'exploded');
    if (g.bombPhase === 'ended' && g.roundEndsAt && now >= g.roundEndsAt) {
      if (Math.max(g.score.red, g.score.blue) >= WIN_ROUNDS) { finishMatch(room); continue; }
      g.round += 1; startRound(room);
    }
    if (room.players.length >= 2) broadcastPositions(room);
  }
}

// ---------------------------------------------------------------- rooms
function removePlayer(room, username) {
  if (room.disc[username]) { clearTimeout(room.disc[username]); delete room.disc[username]; }
  const wasStarted = room.started && !room.over;
  room.players = room.players.filter(n => n !== username);
  for (const k of ['positions', 'health', 'lastShot', 'lastGrenade', 'grenadesThrown', 'inputs', 'teams']) delete room[k][username];
  if (!room.players.length) { rooms.delete(room.code); return; }
  if (wasStarted) {
    // Leaving is not a win condition: close the room, commit only kills/deaths, award nothing.
    room.started = false; room.closed = true;
    commitStats(room, false, null);
    broadcast(room, { type: 'opponent_left', username, winner: null, awardWin: false });
  } else {
    if (room.over) room.closed = true;
    broadcastRoom(room);
  }
}
function leaveRoom(ws) {
  const c = clients.get(ws); if (!c || !c.roomCode) return;
  const room = rooms.get(c.roomCode); c.roomCode = null;
  if (room && c.username) removePlayer(room, c.username);
  send(ws, { type: 'room_left' });
}
function enterRoom(ws, room) {
  const c = clients.get(ws); if (!c || !c.username) return error(ws, 'Сначала войди в аккаунт.');
  if (room.closed || room.over) return error(ws, 'Этот матч уже завершён или закрыт.');
  if (c.roomCode === room.code) return;
  if (room.players.length >= room.maxPlayers) return error(ws, 'Комната заполнена.');
  leaveRoom(ws);
  if (!room.players.includes(c.username)) room.players.push(c.username);
  c.roomCode = room.code;
  if (!room.teams[c.username]) {
    const red = room.players.filter(n => room.teams[n] === 'red').length, blue = room.players.filter(n => room.teams[n] === 'blue').length;
    room.teams[c.username] = red === blue ? (Math.random() < 0.5 ? 'red' : 'blue') : (red < blue ? 'red' : 'blue');
  }
  room.stats[c.username] = room.stats[c.username] || { kills: 0, deaths: 0 };
  resetPlayer(room, c.username);
  room.positions[c.username] = spawnFor(room, c.username);
  broadcastRoom(room);
  send(ws, { type: 'game_state', state: publicState(room) });
  startMatchIfReady(room);
  broadcastPositions(room);
}
function startMatchIfReady(room) {
  if (!room || room.started || room.closed || room.over || room.players.length < 2) return;
  room.started = true; room.mode = 'bomb';
  room.gameState.round = 1; room.gameState.score = { red: 0, blue: 0 };
  broadcast(room, { type: 'match_started', room: roomSnapshot(room), mode: 'bomb', startedAt: Date.now() });
  startRound(room);
}
function createRoom(ws) {
  const c = clients.get(ws); if (!c || !c.username) return error(ws, 'Сначала войди в аккаунт.');
  leaveRoom(ws);
  let code; do { code = randomCode(); } while (rooms.has(code));
  const room = {
    code, mode: 'bomb', maxPlayers: 2, players: [], started: false, closed: false, over: false, statsCommitted: false,
    positions: Object.create(null), health: Object.create(null), lastShot: Object.create(null), lastGrenade: Object.create(null),
    grenadesThrown: Object.create(null), inputs: Object.create(null), teams: Object.create(null), stats: Object.create(null),
    disc: Object.create(null), grenades: [], fires: [],
    gameState: { bombPhase: 'freeze', bomb: null, round: 1, score: { red: 0, blue: 0 }, actions: {}, freezeEndsAt: 0, liveEndsAt: 0, roundEndsAt: null, winner: null, endReason: null }
  };
  rooms.set(code, room); enterRoom(ws, room);
}

// ---------------------------------------------------------------- connection / identity
function bindUser(ws, username) {
  const c = clients.get(ws); if (!c) return;
  if (c.username === username) return;
  // One live connection per account: the newest replaces the old one without leaving the room.
  for (const [other, oc] of clients) {
    if (other !== ws && oc.username === username) { oc.username = null; oc.roomCode = null; try { other.close(4000, 'replaced'); } catch { /* ignore */ } }
  }
  c.username = username;
  for (const room of rooms.values()) {
    if (room.players.includes(username) && !room.closed) {
      c.roomCode = room.code;
      if (room.disc[username]) { clearTimeout(room.disc[username]); delete room.disc[username]; broadcast(room, { type: 'opponent_reconnected', username }); }
      send(ws, { type: 'room_state', room: roomSnapshot(room) });
      send(ws, { type: 'game_state', state: publicState(room) });
      send(ws, positionsPacket(room));
      break;
    }
  }
}
function getAuth(ws, msg) {
  const s = sessions.get(msg.token);
  if (!s || s.expires < Date.now() || !users[s.username]) { error(ws, 'Сначала войди в аккаунт.'); send(ws, { type: 'auth_required' }); return null; }
  bindUser(ws, s.username);
  return s.username;
}

// ---------------------------------------------------------------- message handling
async function handle(ws, msg) {
  if (!msg || typeof msg.type !== 'string') return error(ws, 'Неверный формат сообщения.');
  const client = clients.get(ws); if (!client) return;
  if (msg.type === 'ping') return send(ws, { type: 'pong', now: Date.now() });
  if (msg.type === 'register') {
    if (authThrottled(client.ip)) return error(ws, 'Слишком много попыток. Подожди минуту.');
    const username = typeof msg.username === 'string' ? msg.username.trim() : '';
    const password = msg.password;
    if (!validName(username)) return error(ws, 'Имя: 3–20 символов, латиница, цифры, пробел, _ или -.');
    if (typeof password !== 'string' || password.length < 8 || password.length > 128) return error(ws, 'Пароль должен содержать 8–128 символов.');
    if (Object.keys(users).some(n => n.toLowerCase() === username.toLowerCase())) return error(ws, 'Такое имя уже занято.');
    const pass = await hashPassword(password);
    users[username] = { ...pass, createdAt: new Date().toISOString(), stats: { matches: 0, wins: 0, kills: 0, deaths: 0 } };
    saveUsers(); return send(ws, { type: 'registered' });
  }
  if (msg.type === 'login') {
    if (authThrottled(client.ip)) return error(ws, 'Слишком много попыток. Подожди минуту.');
    const username = typeof msg.username === 'string' ? msg.username.trim() : '';
    const user = users[username];
    if (!user || typeof msg.password !== 'string' || !(await passwordMatches(msg.password, user))) return error(ws, 'Неверное имя или пароль.');
    const token = randomToken(); sessions.set(token, { username, expires: Date.now() + SESSION_TTL_MS });
    client.token = token; bindUser(ws, username);
    return send(ws, { type: 'auth_ok', token, user: safeUser(username) });
  }
  const username = getAuth(ws, msg); if (!username) return;
  if (msg.type === 'resume') return send(ws, { type: 'resumed', user: safeUser(username), room: client.roomCode && rooms.get(client.roomCode) ? roomSnapshot(rooms.get(client.roomCode)) : null });
  if (msg.type === 'create_room') return createRoom(ws);
  if (msg.type === 'join_room') {
    const code = typeof msg.code === 'string' ? msg.code.trim().toUpperCase() : '';
    const room = rooms.get(code); if (!room) return error(ws, 'Комната не найдена. Проверь код.');
    return enterRoom(ws, room);
  }
  if (msg.type === 'leave_room') return leaveRoom(ws);
  if (msg.type === 'get_stats') return send(ws, { type: 'stats', stats: users[username].stats });
  if (msg.type === 'quick_match') {
    leaveRoom(ws);
    const available = [...rooms.values()].find(r => !r.started && !r.closed && !r.over && r.players.length === 1 && r.players[0] !== username);
    if (available) { enterRoom(ws, available); send(ws, { type: 'match_found', room: roomSnapshot(available) }); }
    else { createRoom(ws); const room = rooms.get(client.roomCode); if (room) send(ws, { type: 'match_found', room: roomSnapshot(room) }); }
    return;
  }
  const room = client.roomCode && rooms.get(client.roomCode);
  if (msg.type === 'player_input') {
    if (!room || !room.started) return;
    const i = msg.input || {};
    const yaw = Number(i.yaw), pitch = Number(i.pitch);
    if (!Number.isFinite(yaw) || !Number.isFinite(pitch) || Math.abs(pitch) > 1.7) return;
    const inp = room.inputs[username] || (room.inputs[username] = { jumpAt: 0 });
    inp.forward = i.forward === true; inp.backward = i.backward === true; inp.left = i.left === true; inp.right = i.right === true;
    inp.scoped = i.scoped === true; inp.at = Date.now();
    inp.yaw = Math.atan2(Math.sin(yaw), Math.cos(yaw)); inp.pitch = pitch; // wrap: yaw grows without bound in the browser
    if (i.jump === true) inp.jumpAt = Date.now();
    return;
  }
  if (!room || !room.players.includes(username)) return error(ws, 'Сначала войди в комнату.');
  const g = room.gameState, now = Date.now();
  if (msg.type === 'player_shot') {
    if (!room.started || (g.bombPhase !== 'live' && g.bombPhase !== 'planted')) return;
    const shooter = room.positions[username];
    if (!shooter || !isAlive(room, username)) return;
    const weaponKey = typeof msg.weaponIcon === 'string' && WEAPONS[msg.weaponIcon] ? msg.weaponIcon : 'rifle';
    const weapon = WEAPONS[weaponKey];
    if (now - (room.lastShot[username] || 0) < weapon.rate * 0.6) return;
    room.lastShot[username] = now;
    // Aim at the moment of the click (recoil of this shot not included) — fall back to the latest input.
    let yaw = Number(msg.yaw), pitch = Number(msg.pitch);
    if (!Number.isFinite(yaw) || !Number.isFinite(pitch) || Math.abs(pitch) > 1.7) { yaw = shooter.yaw; pitch = shooter.pitch; }
    const cp = Math.cos(pitch), dir = { x: -Math.sin(yaw) * cp, y: Math.sin(pitch), z: -Math.cos(yaw) * cp };
    const ox = shooter.x, oy = shooter.y + EYE_HEIGHT, oz = shooter.z;
    let best = null;
    for (const target of room.players) {
      if (target === username || teamFor(room, target) === teamFor(room, username) || !isAlive(room, target)) continue;
      const v = room.positions[target]; if (!v) continue;
      const parts = [
        { x: v.x, y: v.y + 1.5, z: v.z, r: 0.38, head: true },
        { x: v.x, y: v.y + 0.85, z: v.z, r: 0.62, head: false },
        { x: v.x, y: v.y + 0.3, z: v.z, r: 0.5, head: false }
      ];
      for (const part of parts) {
        const px = part.x - ox, py = part.y - oy, pz = part.z - oz;
        const along = px * dir.x + py * dir.y + pz * dir.z;
        if (along < 0 || along > weapon.range) continue;
        const miss = Math.hypot(px - dir.x * along, py - dir.y * along, pz - dir.z * along);
        if (miss <= part.r && (!best || along < best.along || (along === best.along && part.head))) best = { target, along, head: part.head };
      }
    }
    if (!best) return;
    if (wallDistance(ox, oy, oz, dir.x, dir.y, dir.z, best.along) < best.along - 0.05) return; // blocked by cover
    applyDamage(room, username, best.target, Math.min(1000, weapon.damage * (best.head ? weapon.head : 1)), weaponKey, best.head);
    return;
  }
  if (msg.type === 'game_event') {
    const event = msg.event, pos = room.positions[username], team = teamFor(room, username);
    if (!isAlive(room, username)) return;
    const nearSite = p => BOMB_SITES.some(([sx, sz]) => Math.hypot(p.x - sx, p.z - sz) < 7);
    if (event === 'bomb_plant_start') {
      if (g.bombPhase !== 'live' || team !== 'red' || !pos || !nearSite(pos)) return error(ws, 'Нельзя начать установку здесь.');
      g.actions[username] = { type: 'plant', startedAt: now, x: pos.x, z: pos.z };
    } else if (event === 'bomb_defuse_start') {
      if (g.bombPhase !== 'planted' || team !== 'blue' || !pos || !g.bomb || distance2(pos, g.bomb) > 4.5) return error(ws, 'Нельзя начать обезвреживание здесь.');
      g.actions[username] = { type: 'defuse', startedAt: now };
    } else if (event === 'bomb_action_cancel') {
      delete g.actions[username];
    } else if (event === 'bomb_planted') {
      const a = g.actions[username];
      if (g.bombPhase !== 'live' || team !== 'red' || !pos || !a || a.type !== 'plant' || now - a.startedAt < PLANT_MS - 250) return error(ws, 'Сервер не подтвердил время установки.');
      if (!nearSite(pos) || Math.hypot(pos.x - a.x, pos.z - a.z) > 3) return error(ws, 'Позиция установки не совпадает с серверной.');
      delete g.actions[username];
      g.bombPhase = 'planted'; g.bomb = { x: pos.x, z: pos.z, plantedAt: now, explodesAt: now + BOMB_FUSE_MS, planter: username };
    } else if (event === 'bomb_defused') {
      const a = g.actions[username];
      if (g.bombPhase !== 'planted' || team !== 'blue' || !pos || !g.bomb || distance2(pos, g.bomb) > 4.5 || !a || a.type !== 'defuse' || now - a.startedAt < DEFUSE_MS - 250) return error(ws, 'Сервер не подтвердил время обезвреживания.');
      delete g.actions[username]; return finishRound(room, 'blue', 'defused');
    } else return; // explosion and round flow belong to the server
    return broadcastGameState(room);
  }
  if (msg.type === 'grenade_throw') {
    const pos = room.positions[username];
    if (!pos || !isAlive(room, username) || (g.bombPhase !== 'live' && g.bombPhase !== 'planted')) return;
    const type = ['flash', 'he', 'molotov', 'smoke'].includes(msg.grenadeType) ? msg.grenadeType : null;
    if (!type) return error(ws, 'Неизвестный тип гранаты.');
    if (now - (room.lastGrenade[username] || 0) < 700) return;
    if ((room.grenadesThrown[username] || 0) >= MAX_GRENADES_PER_ROUND) return;
    room.lastGrenade[username] = now; room.grenadesThrown[username] = (room.grenadesThrown[username] || 0) + 1;
    let yaw = Number(msg.yaw), pitch = Number(msg.pitch);
    if (!Number.isFinite(yaw) || !Number.isFinite(pitch) || Math.abs(pitch) > 1.7) { yaw = pos.yaw; pitch = pos.pitch; }
    const cp = Math.cos(pitch), dir = { x: -Math.sin(yaw) * cp, y: Math.sin(pitch), z: -Math.cos(yaw) * cp };
    const grenade = {
      id: crypto.randomBytes(6).toString('hex'), owner: username, team: teamFor(room, username), type,
      x: pos.x + dir.x * 0.8, y: pos.y + EYE_HEIGHT + dir.y * 0.8, z: pos.z + dir.z * 0.8,
      vx: dir.x * 28.8, vy: dir.y * 28.8 + 10.8, vz: dir.z * 28.8, born: now, fuse: GRENADE_FUSE[type]
    };
    if (pointInSolid(grenade.x, grenade.y, grenade.z)) { grenade.x = pos.x; grenade.y = pos.y + EYE_HEIGHT; grenade.z = pos.z; }
    room.grenades.push(grenade);
    broadcast(room, { type: 'grenade_spawn', grenade: { id: grenade.id, owner: username, team: grenade.team, gtype: type, x: grenade.x, y: grenade.y, z: grenade.z, vx: grenade.vx, vy: grenade.vy, vz: grenade.vz, fuse: grenade.fuse } });
    return;
  }
  return error(ws, 'Неизвестная команда.');
}

// ---------------------------------------------------------------- http (static: only the game page)
const STATIC = { '/': 'index.html', '/index.html': 'index.html' };
const server = http.createServer((req, res) => {
  let pathname = '/';
  try { pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname); } catch { res.writeHead(400); return res.end('Bad request'); }
  if (pathname === '/healthz') { res.writeHead(200, { 'Content-Type': 'text/plain' }); return res.end('ok'); }
  const name = STATIC[pathname];
  if (!name) { res.writeHead(404); return res.end('Not found'); } // server.js and data/users.json are never served
  fs.readFile(path.join(ROOT, name), (err, data) => {
    if (err) { res.writeHead(404); return res.end('Not found'); }
    res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'X-Content-Type-Options': 'nosniff', 'Cache-Control': 'no-store' });
    res.end(data);
  });
});
const wss = new WebSocketServer({ server, maxPayload: MAX_MESSAGE });
wss.on('connection', (ws, req) => {
  const ip = String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
  console.log('[ws] connected', ip);
  ws.isAlive = true;
  const c = { username: null, roomCode: null, token: null, ip, windowStart: Date.now(), count: 0 };
  clients.set(ws, c);
  send(ws, { type: 'info', message: 'Соединение с сервером установлено.' });
  ws.on('pong', () => { ws.isAlive = true; });
  ws.on('message', async raw => {
    ws.isAlive = true;
    const now = Date.now();
    if (now - c.windowStart > 1000) { c.windowStart = now; c.count = 0; }
    if (++c.count > 150) { ws.close(1008, 'rate limit'); return; }
    try { await handle(ws, JSON.parse(raw.toString())); }
    catch (e) { console.error('Message handler error:', e.message); error(ws, 'Внутренняя ошибка сервера.'); }
  });
  ws.on('close', (code, reason) => {
    console.log('[ws] closed', c.username || 'anonymous', code, reason?.toString() || '');
    clients.delete(ws);
    if (!c.username || !c.roomCode) return;
    const room = rooms.get(c.roomCode); if (!room) return;
    if ([...clients.values()].some(o => o.username === c.username && o.roomCode === c.roomCode)) return;
    if (room.started && !room.over && !room.closed) {
      // Grace period: a brief network drop must not forfeit the match.
      broadcast(room, { type: 'opponent_disconnected', username: c.username, graceMs: DISCONNECT_GRACE_MS });
      room.disc[c.username] = setTimeout(() => { delete room.disc[c.username]; removePlayer(room, c.username); }, DISCONNECT_GRACE_MS);
    } else removePlayer(room, c.username);
  });
});
// Keep idle sockets alive through proxies (Render closes silent connections) and drop dead ones.
setInterval(() => {
  for (const ws of wss.clients) {
    if (ws.isAlive === false) { ws.terminate(); continue; }
    ws.isAlive = false; try { ws.ping(); } catch { /* ignore */ }
  }
}, 25000).unref();
setInterval(() => { const now = Date.now(); for (const [t, s] of sessions) if (s.expires < now) sessions.delete(t); for (const [ip, e] of authAttempts) if (now > e.reset) authAttempts.delete(ip); }, 600000).unref();
setInterval(tick, TICK_MS).unref();
process.on('uncaughtException', e => console.error('[fatal-ish] uncaughtException:', e));
process.on('unhandledRejection', e => console.error('[fatal-ish] unhandledRejection:', e));
server.listen(PORT, HOST, () => console.log(`CS2 Bomb Mode Arena v35 server: http://${HOST}:${PORT}`));
