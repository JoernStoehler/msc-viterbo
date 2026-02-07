# Rust Algorithms Reference

Quick reference for algorithms in `packages/rust_viterbo/`.

## Crate Organization

| Crate | Purpose |
|-------|---------|
| `geom` | Clean reference library (symplectic + euclidean geometry, 2D + 4D) |
| `hk2017` | HK2017 algorithm (works on any polytope with 0 ∈ int K) |
| `tube` | Tube algorithm (polytopes without Lagrangian 2-faces) |
| `billiard` | Minkowski billiard algorithm for Lagrangian products (draft, see SPEC.md) |
| `ffi` | PyO3/Maturin bindings |

## Algorithm Comparison

| Property | HK2017 | Tube |
|----------|--------|------|
| **Inputs** | H-rep (normals, heights), 0 ∈ int K | H-rep, no Lagrangian 2-faces |
| **Outputs** | Capacity + optimal β weights | Capacity + closed Reeb orbit |
| **Performance** | O(F!) permutations, ~1µs each. Practical limit ~10 facets | Branch-and-bound, varies |
| **Trust level** | High (validated against literature) | High (cross-validated with HK2017) |
| **Knobs** | `naive` vs `graph_pruned` enumeration | Tolerance constants in `tube/src/constants.rs` |
| **References** | Thesis §algorithms, HK2017 paper (arXiv:1712.03494) | Thesis §algorithms, CH2021 (arXiv:2008.10111) |

**Note:** Billiard algorithm has design spec in `billiard/SPEC.md`, implementation tracked in issue #92.

## Philosophy: geom as Reference

Algorithms should use geom when it fits, but **copy and customize** when algorithm-specific needs diverge (e.g., different tolerances, extra fields).

Why: algorithms have different numerical requirements; forcing shared abstractions adds complexity without benefit. geom exists to orient against, making deviations explicit.

**Duplication is acceptable when purposeful.** Value of geom: clean code to orient against, making deviations obvious and intentional.
