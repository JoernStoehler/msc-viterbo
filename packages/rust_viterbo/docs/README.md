# Rust Viterbo Documentation

EHZ capacity algorithms for convex polytopes.

## Status

| Crate | Domain | Tests | FFI |
|-------|--------|-------|-----|
| **billiard** | Lagrangian products K₁ × K₂ | ✅ Pass | Stub |
| **hk2017** | Any polytope | ✅ Pass | ✅ Working |
| **tube** | Non-Lagrangian polytopes | ✅ Pass | Stub |
| **geom** | Shared polytope types | ✅ Pass | N/A |

**Next:** Wire up billiard and tube FFI to enable Python experiments.

## Documents

| File | Purpose |
|------|---------|
| [developer-spec-v2.md](developer-spec-v2.md) | Algorithm specifications |
| [trivialization-derivation.md](trivialization-derivation.md) | 2-face trivialization formula |

**Debugging history** (useful if you hit similar bugs):
- [findings-orbit-validation-2026-01-26.md](findings-orbit-validation-2026-01-26.md)
- [findings-trivialization-bug-2026-01-26.md](findings-trivialization-bug-2026-01-26.md)

## Related

- **Thesis:** `packages/latex_viterbo/`
- **Python:** `packages/python_viterbo/`
