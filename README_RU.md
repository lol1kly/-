# CS2 Bomb Mode Arena v25 — Multiplayer integration

## Files
- `index.html` — the v25 game, preserving cases, inventory, 3D FPS arena, bots, weapons, grenades, bomb/hostage modes, plus online player position and hit synchronization.
- `CS2_Bomb_Mode_Arena_v25_MULTIPLAYER_STAGE.html` — same complete game as a separately named HTML file.
- `server.js` — HTTP + WebSocket server for accounts, rooms, quick match, position snapshots and player-hit events.
- `package.json` — Node.js dependencies and start command.

## Run locally
Requires Node.js 18+:
1. Extract the ZIP.
2. Open a terminal in this folder.
3. Run `npm install`
4. Run `npm start`
5. Open `http://localhost:3000` in a browser.
6. In the Online tab, connect to `ws://localhost:3000`, register/login, create a room and join from another browser/device on the same network using the host computer's LAN IP and port 3000.

## Deploy on Render
Create a **Web Service** from the GitHub repository:
- Runtime: Node
- Build command: `npm install`
- Start command: `npm start`
- No static-site deployment; this needs a persistent Node WebSocket server.
When deployed on HTTPS, the client defaults to `wss://<your-render-host>` when you open the Online tab. Use the same public URL in the server address field if it does not fill automatically.

## Important status
This is an integrated multiplayer prototype, not a certified production-grade competitive server. It synchronizes remote player positions and hit/health events within a room. The hit event is still client-reported and is not authoritative anti-cheat; round state, bomb planting/defusing, grenades, inventory, case openings and all bot AI are not fully server-authoritative/shared between clients yet. The original local gameplay remains available. Test with two browser sessions before sharing publicly.
