#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"

if ! command -v lake >/dev/null 2>&1; then
  printf 'lake not found; skipping Lean prep\n' >&2
  exit 0
fi

SHARED_BASE=/workspaces/worktrees/shared/lean
SHARED_PKGS="$SHARED_BASE/packages"
mkdir -p "$SHARED_PKGS"
mkdir -p .lake

# If a local packages dir exists (e.g., from a prior build), seed the shared cache once
if [[ -d .lake/packages && ! -L .lake/packages ]]; then
  if [[ -z "$(ls -A "$SHARED_PKGS" 2>/dev/null)" ]]; then
    echo "[lean] seeding shared packages cache from existing .lake/packages"
    mv .lake/packages/* "$SHARED_PKGS"/ 2>/dev/null || true
  fi
  rm -rf .lake/packages
fi

# Link packages to shared location so mathlib downloads happen only once
if [[ ! -e .lake/packages ]]; then
  ln -s "$SHARED_PKGS" .lake/packages
fi

echo '[lean] fetching community cache (mathlib, dependencies)'
if ! lake exe cache get; then
  echo '[lean] cache download failed; you can run `lake exe cache get` or `lake build` manually when needed.'
  exit 0
fi

echo '[lean] prep done (no build run by default)'
