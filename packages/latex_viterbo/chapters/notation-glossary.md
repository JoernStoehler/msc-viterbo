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
| `c_EHZ(K)` | Ekeland-Hofer-Zehnder capacity |
| `sys(K)` | Systolic ratio: c_EHZ(K)² / (2 · Vol(K)) |

## Key Terms

| Term | Definition |
|------|------------|
| Lagrangian product | K = K₁ × K₂ where K₁ ⊂ R²_q, K₂ ⊂ R²_p (q and p planes decoupled) |
| Lagrangian 2-face | 2-face where ω(n_i, n_j) = 0 for its two bounding facet normals |
| Reeb orbit | Closed trajectory on ∂K following Reeb dynamics (piecewise linear for polytopes) |
| Clarke dual | Dual formulation: min action over closed curves ↔ max over β weights |
| Rotation number | How many times orbit "winds" around; integer for closed orbits |

## Cross-Paper Notation

| This thesis | HK2017 | CH2021 | Notes |
|-------------|--------|--------|-------|
| `F` (# facets) | `m` | `n` | |
| `β_i` | `t_i` | — | Time weights |
| `Q` | `Q` | — | Same |
| `σ` | `σ` | — | Permutation |

## Open Issues

1. **Missing theorems**: `\todoref{thm:simple-min-action-reeb-orbit}`, `\todoref{thm:cz-index}` in algorithms.tex need theorems written in math chapters.
