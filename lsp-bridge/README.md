# Lean LSP Bridge (Node)

Persistent HTTP bridge to a Lean LSP server. Each session owns one Lean server process.

## Requirements
- Lean 4 + Lake installed on the VPS (via elan recommended).
- Mathlib in the project workspace you point the server at.

## Setup
```sh
cd lsp-bridge
npm install
```

Create a `.env` file in `lsp-bridge/` (recommended for secrets):
```sh
PORT=8787
HOST=127.0.0.1
LEAN_PROJECT_ROOT=/path/to/lean/project
LEAN_PROJECT_URI=file:///path/to/lean/project
LEAN_SERVER_CMD=/root/.elan/bin/lean
LEAN_SERVER_ARGS=--server
LEAN_GOALS_METHOD=$/lean/plainGoal
LEAN_BRIDGE_TOKEN=replace-me
ALLOWED_ORIGINS=https://your-domain.vercel.app,https://your-custom-domain.com
```

Start:
```sh
npm start
```

## Endpoints
- `POST /session` → `{ sessionId }`
- `POST /session/open` → `{ uri, text }`
- `POST /session/change` → `{ uri, text }`
- `POST /session/request` → `{ method, params }`
- `POST /session/notify` → `{ method, params }`
- `POST /session/goals` → `{ uri, position }`
- `POST /session/close` → `{ sessionId }`
- `GET /health`

## Notes
- The bridge assumes full-document updates on `didChange`.
- `LEAN_GOALS_METHOD` can be overridden if your Lean server uses a different goal request.
- Use `LEAN_BRIDGE_TOKEN` to require an `x-lean-bridge-token` header on all requests.
- Use `ALLOWED_ORIGINS` to restrict browser-originated traffic.
- Set `HOST=127.0.0.1` to keep the service off the public internet.
