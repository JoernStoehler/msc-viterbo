#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"

if ! command -v uv >/dev/null 2>&1; then
  printf 'uv not found; skipping python prep\n' >&2
  exit 0
fi

printf '[python] syncing env (uv sync --locked --extra dev)\n'
uv sync --locked --extra dev
printf '[python] done\n'
