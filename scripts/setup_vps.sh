#!/usr/bin/env bash
set -euo pipefail

REPO_URL="${REPO_URL:-https://github.com/Andrewp2/lean-experiment.git}"
APP_DIR="${APP_DIR:-/opt/lean-experiment}"
BRIDGE_DIR="${BRIDGE_DIR:-$APP_DIR/lsp-bridge}"
LEAN_PROJECT_ROOT="${LEAN_PROJECT_ROOT:-/opt/lean-workspace}"
NODE_MAJOR="${NODE_MAJOR:-20}"

echo "==> Installing system dependencies"
apt-get update
apt-get install -y --no-install-recommends \
  ca-certificates \
  curl \
  git \
  build-essential \
  pkg-config \
  libssl-dev

echo "==> Installing Node.js ${NODE_MAJOR}.x"
curl -fsSL "https://deb.nodesource.com/setup_${NODE_MAJOR}.x" | bash -
apt-get install -y nodejs

echo "==> Installing elan (Lean toolchain manager)"
if [ ! -d "/root/.elan" ]; then
  curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y
fi
export PATH="/root/.elan/bin:$PATH"
elan default stable

echo "==> Cloning repo"
if [ ! -d "$APP_DIR" ]; then
  git clone "$REPO_URL" "$APP_DIR"
else
  cd "$APP_DIR"
  git pull --ff-only || true
fi

echo "==> Installing LSP bridge dependencies"
cd "$BRIDGE_DIR"
npm install

echo "==> Preparing Lean workspace (placeholder)"
mkdir -p "$LEAN_PROJECT_ROOT"
if [ ! -f "$LEAN_PROJECT_ROOT/lakefile.lean" ]; then
  cd "$LEAN_PROJECT_ROOT"
  lake init lean_workspace
fi

echo "==> Writing systemd service"
cat >/etc/systemd/system/lean-lsp-bridge.service <<EOF
[Unit]
Description=Lean LSP Bridge
After=network.target

[Service]
Type=simple
WorkingDirectory=${BRIDGE_DIR}
Environment=PORT=8787
Environment=LEAN_PROJECT_ROOT=${LEAN_PROJECT_ROOT}
Environment=LEAN_PROJECT_URI=file://${LEAN_PROJECT_ROOT}
Environment=LEAN_SERVER_CMD=/root/.elan/bin/lean
Environment=LEAN_SERVER_ARGS=--server
Environment=LEAN_GOALS_METHOD=\$/lean/plainGoal
ExecStart=/usr/bin/node ${BRIDGE_DIR}/server.mjs
Restart=always
RestartSec=2

[Install]
WantedBy=multi-user.target
EOF

systemctl daemon-reload
systemctl enable --now lean-lsp-bridge

echo "==> Done. Service status:"
systemctl --no-pager status lean-lsp-bridge || true
