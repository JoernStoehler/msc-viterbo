# Rust Viterbo Documentation

Documentation for the `rust_viterbo` package - EHZ capacity computation for convex polytopes.

> **Status (2026-01-27):** Three algorithm crates implemented and tested. FFI exposes HK2017; billiard and tube FFI bindings not yet wired up.

---

## Quick Navigation

| Document | Purpose | When to Read |
|----------|---------|--------------|
| **[developer-spec-v2.md](developer-spec-v2.md)** | Algorithm specifications (all three) | Implementing or modifying algorithms |
| [mathematical-claims.md](mathematical-claims.md) | Mathematical claims with citations | Verifying correctness |
| [trivialization-derivation.md](trivialization-derivation.md) | Correct trivialization formula | Understanding tube algorithm geometry |
| [findings-*.md](.) | Session notes on bugs found and fixed | Learning from debugging history |
| [ffi-contract.md](ffi-contract.md) | Python FFI API contract | Calling from Python |

---

## Current Status

| Crate | Domain | Rust Tests | FFI Exposed |
|-------|--------|------------|-------------|
| **billiard** | Lagrangian products K₁ × K₂ | ✅ All pass (tesseract=4.0, pentagon=3.441) | ❌ Stub |
| **hk2017** | Any polytope | ✅ All pass (tesseract=4.0) | ✅ Working |
| **tube** | Generic polytopes (non-Lagrangian 2-faces) | ✅ All pass | ❌ Stub |
| **geom** | Polytope representation, tolerances | ✅ All pass | N/A |

**Next step:** Wire up billiard and tube FFI bindings to enable Python experiments.

---

## Archived Documentation

These documents describe the v0.1.0 implementation which was deleted. They may be useful for historical context but **do not reflect current code**:

- `implementation-status.md` — Status of archived v0.1.0 (marked ARCHIVED at top)
- `developer-spec.md` — Old spec, superseded by developer-spec-v2.md

---

## Related Documentation

- **Thesis:** `packages/latex_viterbo/` (especially `chapters/algorithms.tex`)
- **Python experiments:** `packages/python_viterbo/`
