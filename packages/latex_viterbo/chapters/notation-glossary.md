# Notation Glossary for Thesis

This file tracks notation conventions to maintain consistency across chapters.

## Polytope Notation

| Symbol | Meaning | Notes |
|--------|---------|-------|
| `K` | Convex polytope in R^4 | Always K for the main polytope |
| `F` | Number of facets | **Use F, not n** (n conflicts with normal vectors) |
| `F_i` | The i-th facet (a 3-face) | i ∈ {1,...,F} |
| `n_i` | Outward unit normal of facet F_i | |
| `h_i` | Height (support value) of facet F_i | h_i > 0, origin in interior |

## Orbit/Trajectory Notation

| Symbol | Meaning | Notes |
|--------|---------|-------|
| `k` | Number of participating facets in orbit | k = |S| where S ⊆ {1,...,F} |
| `S` | Subset of participating facet indices | S ⊆ {1,...,F} |
| `σ` | Cyclic ordering (permutation) of S | σ: {1,...,k} → S |
| `β_i` | Normalized time coefficient for facet i | β_i ≥ 0, Σβ_i h_i = 1 |
| `T_i` | Actual time spent with facet i's velocity | Before normalization |

## Symplectic Notation

| Symbol | Meaning | Notes |
|--------|---------|-------|
| `J` | Standard complex structure on R^4 | J(q1,q2,p1,p2) = (-p1,-p2,q1,q2) |
| `ω` | Standard symplectic form | ω(x,y) = ⟨Jx, y⟩ or ½⟨Jx,y⟩? CHECK |
| `p_i` | Reeb vector for facet F_i | p_i = (2/h_i) J n_i |
| `λ` | Liouville form | λ = ½(q dp - p dq) |

## Capacity/Action Notation

| Symbol | Meaning | Notes |
|--------|---------|-------|
| `c_EHZ(K)` | Ekeland-Hofer-Zehnder capacity | = min action over closed characteristics |
| `A(γ)` | Action of curve γ | A = ∫ λ |
| `Q(σ,β)` | Quadratic form in HK formula | c_EHZ = (2 Q_max)^{-1} |
| `sys(K)` | Systolic ratio | sys = c_EHZ²/(2·vol) |

## Face Notation

| Symbol | Meaning | Notes |
|--------|---------|-------|
| `k-face` | k-dimensional face | 3-face = facet, 0-face = vertex |
| `F_i ∩ F_j` | 2-face (if non-empty interior) | Intersection of two facets |

## Known Issues to Fix

1. **Section 3.1** uses `n` for facet count → change to `F`
2. **Section 3.4** uses `n` for facet count → change to `F`
3. **Factor of 2 in ω**: Check if ω(x,y) = ⟨Jx,y⟩ or ½⟨Jx,y⟩ throughout
