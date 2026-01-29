# Rust Viterbo Documentation

EHZ capacity algorithms for convex polytopes.

## Status

| Crate | Domain | Tests | FFI |
|-------|--------|-------|-----|
| **hk2017** | Any polytope | ✅ Pass | ✅ Working |
| **tube** | Non-Lagrangian polytopes | ✅ Pass | ✅ Working |
| **geom** | Shared polytope types | ✅ Pass | N/A |

**Note:** Billiard algorithm was deleted pending reimplementation from thesis spec (see issue #92).

## Documents

| File | Purpose |
|------|---------|
| [developer-spec-v2.md](developer-spec-v2.md) | Algorithm specifications |
| [trivialization-derivation.md](trivialization-derivation.md) | 2-face trivialization formula |

## Related

- **Thesis:** `packages/latex_viterbo/`
- **Python:** `packages/python_viterbo/`
