#!/usr/bin/env bash
# Run Rust tests with per-test timing output.
#
# Usage:
#   ./scripts/test-rust.sh           # Run debug + release tests
#   ./scripts/test-rust.sh --debug   # Run only debug-mode tests
#   ./scripts/test-rust.sh --release # Run only release-mode tests
#
# Test mode separation:
#   Tests are self-documenting via #[cfg_attr(debug_assertions, ignore)]:
#   - Debug mode: skips tests marked with this attribute
#   - Release mode: runs tests marked with this attribute
#
# Pattern rationale:
#   DEBUG MODE tests exercise code paths with debug_assert!() checks
#   RELEASE MODE tests verify output correctness (expensive, no debug dependency)

set -euo pipefail
cd "$(dirname "$0")/../packages/rust_viterbo"

RUN_DEBUG=true
RUN_RELEASE=true

for arg in "$@"; do
    case $arg in
        --debug) RUN_RELEASE=false ;;
        --release) RUN_DEBUG=false ;;
        --help|-h)
            head -16 "$0" | tail -15
            exit 0
            ;;
    esac
done

if [[ "$RUN_DEBUG" == "true" ]]; then
    echo ""
    echo "════════════════════════════════════════════════════════════════"
    echo "  DEBUG MODE TESTS (with debug_assert! checks)"
    echo "════════════════════════════════════════════════════════════════"
    cargo test --workspace --exclude rust_viterbo_ffi
fi

if [[ "$RUN_RELEASE" == "true" ]]; then
    echo ""
    echo "════════════════════════════════════════════════════════════════"
    echo "  RELEASE MODE TESTS (expensive output-verification tests)"
    echo "════════════════════════════════════════════════════════════════"
    cargo test --release --workspace --exclude rust_viterbo_ffi
fi

echo ""
echo "════════════════════════════════════════════════════════════════"
echo "  DONE"
echo "════════════════════════════════════════════════════════════════"
