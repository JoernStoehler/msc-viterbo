#!/usr/bin/env bash
# Catnip setup.sh - executed when catnip creates a new workspace.
# See: https://github.com/wandb/catnip
#
# This script runs in the workspace directory after catnip clones/creates it.
# Use it to install dependencies or configure the workspace.
#
# CURRENTLY DISABLED: Uncomment sections below when ready to use.
# Reason: Avoid 10+ minute startup delays from Rust compilation.

set -euo pipefail

echo "[setup.sh] Catnip workspace setup starting..."

# -----------------------------------------------------------------------------
# Python dependencies (fast, ~30s)
# -----------------------------------------------------------------------------
# if [[ -d packages/python_viterbo ]]; then
#   echo "[setup.sh] Installing Python dependencies..."
#   (cd packages/python_viterbo && uv sync --locked --extra dev)
# fi

# -----------------------------------------------------------------------------
# Rust dependencies (slow, ~10min on cold cache)
# -----------------------------------------------------------------------------
# if [[ -d packages/rust_viterbo ]]; then
#   echo "[setup.sh] Fetching Rust dependencies..."
#   cargo fetch --manifest-path packages/rust_viterbo/Cargo.toml
#
#   # Optional: build to warm cache (very slow)
#   # echo "[setup.sh] Building Rust workspace..."
#   # cargo build --manifest-path packages/rust_viterbo/Cargo.toml
# fi

echo "[setup.sh] Catnip workspace setup complete (dependencies not installed - see setup.sh to enable)."
