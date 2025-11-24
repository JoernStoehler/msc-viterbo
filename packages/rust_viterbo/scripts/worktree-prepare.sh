#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)
REPO_ROOT=$(cd "$SCRIPT_DIR/../../.." && pwd)
PACKAGE_ROOT=$(cd "$SCRIPT_DIR/.." && pwd)

TARGET_DIR="$REPO_ROOT/../worktrees/shared/target"
mkdir -p "$TARGET_DIR"

if ! command -v cargo >/dev/null 2>&1; then
  printf 'cargo not found; skipping Rust prep\n' >&2
  exit 0
fi

echo "[rust] using shared target dir: $TARGET_DIR"
CARGO_TARGET_DIR="$TARGET_DIR" cargo fetch --manifest-path "$PACKAGE_ROOT/Cargo.toml"
echo '[rust] done'
