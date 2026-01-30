#!/usr/bin/env bash
# Local CI: mirrors .github/workflows/ci.yml
#
# Usage:
#   ./scripts/ci.sh           # Run all checks
#   ./scripts/ci.sh --rust    # Rust only (fmt, clippy, tests)
#   ./scripts/ci.sh --python  # Python only (lint, typecheck, ffi, pytest)
#
# Goal: "local ci.sh passes" implies "remote CI will pass"

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

RUN_RUST=true
RUN_PYTHON=true

for arg in "$@"; do
    case $arg in
        --rust) RUN_PYTHON=false ;;
        --python) RUN_RUST=false ;;
        --help|-h)
            head -10 "$0" | tail -9
            exit 0
            ;;
    esac
done

FAILED=()

section() {
    echo ""
    echo "════════════════════════════════════════════════════════════════"
    echo "  $1"
    echo "════════════════════════════════════════════════════════════════"
}

run_step() {
    local name="$1"
    shift
    echo "→ $name"
    if "$@"; then
        echo "  ✓ $name"
    else
        echo "  ✗ $name FAILED"
        FAILED+=("$name")
    fi
}

# ─────────────────────────────────────────────────────────────────────────────
# Rust checks (matches ci.yml rust job)
# ─────────────────────────────────────────────────────────────────────────────
if [[ "$RUN_RUST" == "true" ]]; then
    section "RUST"
    cd "$REPO_ROOT/packages/rust_viterbo"

    run_step "cargo fmt --check" \
        cargo fmt --all --check

    run_step "cargo clippy" \
        cargo clippy --workspace --exclude rust_viterbo_ffi -- -D warnings

    run_step "cargo test (debug)" \
        cargo test --workspace --exclude rust_viterbo_ffi

    run_step "cargo test (release)" \
        cargo test --release --workspace --exclude rust_viterbo_ffi
fi

# ─────────────────────────────────────────────────────────────────────────────
# Python + FFI checks (matches ci.yml ffi job)
# ─────────────────────────────────────────────────────────────────────────────
if [[ "$RUN_PYTHON" == "true" ]]; then
    section "PYTHON + FFI"
    cd "$REPO_ROOT/packages/python_viterbo"

    run_step "uv sync" \
        uv sync --extra dev

    run_step "ruff check" \
        uv run ruff check src tests

    run_step "pyright" \
        uv run pyright src tests

    run_step "maturin develop (FFI)" \
        uv run maturin develop --manifest-path ../rust_viterbo/ffi/Cargo.toml

    run_step "pytest" \
        uv run pytest -v
fi

# ─────────────────────────────────────────────────────────────────────────────
# Summary
# ─────────────────────────────────────────────────────────────────────────────
section "SUMMARY"

if [[ ${#FAILED[@]} -eq 0 ]]; then
    echo "All checks passed."
    exit 0
else
    echo "Failed checks:"
    for f in "${FAILED[@]}"; do
        echo "  - $f"
    done
    exit 1
fi
