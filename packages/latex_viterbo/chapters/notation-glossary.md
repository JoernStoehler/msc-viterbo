# Notation Glossary

Quick reference for notation used in this thesis and correspondence with key papers.

## Core Symbols (This Thesis)

| Symbol | Meaning |
|--------|---------|
| `K` | Convex polytope in R^4 |
| `F` | Number of facets |
| `F_i`, `n_i`, `h_i` | Facet, its outward unit normal, its height |
| `p_i = (2/h_i) J n_i` | Reeb vector for facet i |
| `k`, `S`, `σ` | # participating facets, subset, cyclic ordering |
| `β_i` | Normalized time coefficient (Σβ_i h_i = 1) |
| `Q(σ,β)` | Quadratic form; c_EHZ = (2 Q_max)^{-1} |
| `ω(x,y) = ⟨Jx, y⟩` | Standard symplectic form |
| `J` | Complex structure: J(q,p) = (-p, q) |

## Cross-Paper Notation

| This thesis | HK2017 | CH2021 | Notes |
|-------------|--------|--------|-------|
| `F` (# facets) | `m` | `n` | |
| `β_i` | `t_i` | — | Time weights |
| `Q` | `Q` | — | Same |
| `σ` | `σ` | — | Permutation |

## Open Issues

1. ~~**ω factor of 2**~~: Fixed. Now ω(x,y) = ⟨Jx, y⟩ everywhere (no ½).
2. **Missing theorems**: `\todoref{thm:simple-min-action-reeb-orbit}`, `\todoref{thm:cz-index}` in algorithms.tex.
