#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"

if ! command -v npm >/dev/null 2>&1; then
  printf 'npm not found; skipping docs-site prep\n' >&2
  exit 0
fi

if [[ ! -f package.json ]]; then
  printf '[docs-site] package.json missing; skipping npm install\n'
  exit 0
fi

printf '[docs-site] installing node deps (npm install)\n'
npm install
printf '[docs-site] done\n'
