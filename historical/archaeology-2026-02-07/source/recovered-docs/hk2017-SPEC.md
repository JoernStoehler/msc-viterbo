# hk2017 — Haim-Kislev 2017 Quadratic Programming Algorithm

**Status:** Implementation complete

## Purpose

Compute EHZ capacity for **any** 4D convex polytope using the quadratic programming approach from Haim-Kislev 2017.

This is the most general algorithm — it works on all polytopes regardless of 2-face character. However, it has factorial complexity O(F!) in the number of facets, limiting practical use to ~10 facets.

## Spec Dependencies

> **Prerequisite reading:** [geom/SPEC.md](../geom/SPEC.md) defines foundational concepts used here:
> - Polytope H-representation
> - Symplectic form ω(·,·)
> - 2-faces and Lagrangian classification
> - Closed Reeb orbits and simple orbits
> - Action = period for Reeb flow
>
> This spec extends those foundations with HK2017-specific concepts:
> - Q-function and its maximization
> - KKT constraints and solver
> - Permutation enumeration strategies

## Theoretical Foundation

**Source:** Haim-Kislev, P. "On the Symplectic Size of Convex Polytopes." *Geometric and Functional Analysis* 29 (2019): 440-463. arXiv:1712.03494 (December 2017).

**Main theorem (HK2017 Theorem 1):** For a convex polytope K ⊂ ℝ⁴:
```
c_EHZ(K) = (1/2) · [max_{σ,β} Q(σ, β)]⁻¹
```

where:
- σ is a permutation of a subset of facets
- β are non-negative coefficients satisfying closure constraints
- Q is a quadratic form involving the symplectic form

---

## The Q-Function

For a permutation σ of facet subset S and coefficients β:

```
Q(σ, β) = Σ_{j<i} β_{σ(i)} · β_{σ(j)} · ω(n_{σ(i)}, n_{σ(j)})
```

where ω(·,·) is the symplectic form.

**Interpretation:** Q measures the symplectic area enclosed by the orbit visiting facets in order σ with coefficients β.

---

## Constraints on β

The coefficients β must satisfy:

1. **Non-negativity:** βᵢ ≥ 0

2. **Height normalization:** Σᵢ βᵢ · hᵢ = 1

3. **Closure (4 equations):** Σᵢ βᵢ · nᵢ = 0 (vector equation in ℝ⁴)

```rust
struct Constraints {
    // Σ βᵢ hᵢ = 1
    height_sum: f64,

    // Σ βᵢ nᵢ = 0 (each coordinate)
    closure: Vector4<f64>,
}
```

---

## Algorithm

```
hk2017_capacity(K):
    best_q = 0

    for each subset S of facets:
        for each permutation σ of S:
            // Solve KKT conditions for this (S, σ)
            β = solve_kkt(S, σ, K)

            if β exists and all βᵢ > 0:
                q = compute_Q(σ, β)
                if q > best_q:
                    best_q = q

    return (1/2) / best_q
```

**Code:** `algorithm.rs:hk2017_capacity()`

### KKT Solver

For fixed (S, σ), we solve a linear system derived from the KKT conditions:

```rust
fn solve_kkt(
    subset: &[usize],
    permutation: &[usize],
    facet_data: &FacetData,
) -> Option<Vec<f64>> {
    // Build and solve the KKT system
    // Returns None if constraints are infeasible
    // Returns Some(beta) if a solution exists
}
```

**Code:** `solve.rs`

### Enumeration Strategies

Two strategies for enumerating (subset, permutation) pairs:

1. **Naive:** All subsets × all permutations of each subset
   - Complexity: O(Σₖ C(F,k) · k!) ≈ O(F!)
   - Guaranteed complete

2. **Graph-pruned:** Build facet transition graph, enumerate only valid cycles
   - Uses facet adjacency to prune impossible transitions
   - Faster when graph is sparse
   - May miss solutions for degenerate polytopes

```rust
pub enum EnumerationStrategy {
    Naive,
    GraphPruned,
}

impl Hk2017Config {
    pub fn naive() -> Self { ... }
    pub fn graph_pruned() -> Self { ... }
}
```

**Code:** `enumerate/naive.rs`, `enumerate/graph.rs`

---

## Correctness of Interior-Only Search

The algorithm only checks interior critical points (all βᵢ > 0), not boundary cases (some βᵢ = 0).

**Why this is correct:** If β* has some βⱼ = 0, then:
- Constraints remain satisfied after dropping facet j
- Q value unchanged (zero terms contribute nothing)
- β* corresponds to interior point in smaller subset S' = S \ {j}

By searching all subsets, boundary cases are covered via smaller subsets.

**Proof:** Thesis Section 3.3, Lemma `lem:hk-boundary`.

---

## Data Structures

```rust
/// Preprocessed facet data for HK2017.
pub struct FacetData {
    pub normals: Vec<Vector4<f64>>,
    pub heights: Vec<f64>,
    pub omega: Vec<Vec<f64>>,        // ω(nᵢ, nⱼ) precomputed
    pub lagrangian_pairs: Vec<(usize, usize)>,  // Pairs where ω ≈ 0
}

/// Result of HK2017 computation.
pub struct Hk2017Result {
    pub capacity: f64,
    pub q_max: f64,
    pub optimal_permutation: Vec<usize>,
    pub optimal_beta: Vec<f64>,
    pub permutations_checked: usize,
    pub permutations_feasible: usize,
}
```

**Code:** `types.rs`

---

## API

```rust
use hk2017::{hk2017_capacity, Hk2017Config, PolytopeHRep};

let hrep = PolytopeHRep::new(normals, heights);
let config = Hk2017Config::naive();  // or graph_pruned()

match hk2017_capacity(&hrep, &config) {
    Ok(result) => {
        println!("Capacity: {}", result.capacity);
        println!("Optimal permutation: {:?}", result.optimal_permutation);
    }
    Err(e) => eprintln!("Error: {}", e),
}
```

---

## Verification

Results can be verified against constraints:

```rust
impl Hk2017Result {
    pub fn verify_checked(&self, facet_data: &FacetData) -> Result<(), VerificationError> {
        // Check β ≥ 0
        // Check Σ βᵢ hᵢ = 1
        // Check Σ βᵢ nᵢ = 0
        // Check Q(σ, β) = q_max
    }
}
```

**Code:** `verify.rs`

---

## Testing Strategy

### Ground Truth Tests

| Polytope | Expected Capacity | Test |
|----------|-------------------|------|
| Tesseract [-1,1]⁴ | 4.0 | `test_full_pipeline_tesseract` |
| Scaled tesseract | λ² · 4.0 | `test_scaling_axiom` |

### Correctness Tests

| Test | Purpose | Location |
|------|---------|----------|
| Enumeration strategies agree | Naive and graph-pruned give same result | `test_enumeration_strategies_agree` |
| Capacity positive | c > 0 for valid polytopes | `test_capacity_positive` |
| Result verification | β satisfies constraints | `verify.rs` tests |

### Property Tests

| Property | Formula | Test |
|----------|---------|------|
| Scaling | c(λK) = λ²c(K) | `test_scaling_axiom` |

---

## Complexity

- **Naive enumeration:** O(Σₖ C(F,k) · k!) ≈ O(F!) — factorial in facet count
- **Graph-pruned:** Depends on graph structure, often much faster

**Practical limit:** ~10 facets for naive, ~15-20 for graph-pruned on typical polytopes.

---

## Known Limitations

1. **Factorial complexity:** Cannot handle large polytopes (>10-15 facets)

2. **Graph-pruned incompleteness:** May miss solutions for degenerate polytopes where the optimal orbit uses non-adjacent facets

3. **Numerical sensitivity:** KKT solver may fail near degenerate configurations

---

## Tolerances

```rust
pub const EPS: f64 = 1e-10;              // General tolerance
pub const CONSTRAINT_TOL: f64 = 1e-8;    // Constraint satisfaction
pub const POSITIVE_TOL: f64 = 1e-10;     // β > 0 check
pub const LAGRANGIAN_TOL: f64 = 1e-9;    // |ω| < tol means Lagrangian
```

**Code:** `types.rs`

---

## Dependencies

- `nalgebra`: Linear algebra
- `geom`: Shared polytope types

---

## Related

- **Shared primitives:** `packages/rust_viterbo/geom/`
- **Tube algorithm:** `packages/rust_viterbo/tube/` (faster for non-Lagrangian polytopes)
- **Billiard algorithm:** `packages/rust_viterbo/billiard/` (faster for Lagrangian products)
- **Reference implementation:** https://github.com/pazithaimkislev/EHZ-capacity
