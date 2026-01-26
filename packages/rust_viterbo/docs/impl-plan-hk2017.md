# Implementation Plan: HK2017 Crate

> **Companion to:** `spec-hk2017.md`
> **Author:** Claude Code agent
> **Date:** 2026-01-26
> **Status:** Implementation complete (naive enumeration works; graph pruning has known limitations)

---

## Overview

This document describes the concrete implementation approach for the HK2017 algorithm
as specified in `spec-hk2017.md`. It captures decisions, clarifications, and deviations.

---

## 1. Crate Structure

```
packages/rust_viterbo/hk2017/
├── Cargo.toml
├── src/
│   ├── lib.rs           # Public API, re-exports
│   ├── types.rs         # PolytopeHRep, Hk2017Config, Hk2017Result, Hk2017Error
│   ├── symplectic.rs    # J matrix, symplectic form, Reeb vectors
│   ├── preprocess.rs    # FacetData computation and validation
│   ├── enumerate/
│   │   ├── mod.rs       # EnumerationStrategy trait
│   │   ├── naive.rs     # Brute-force subset permutation enumeration
│   │   └── graph.rs     # Facet adjacency graph, cycle enumeration
│   ├── solve.rs         # KKT system construction and solution
│   ├── verify.rs        # Result verification (constraint satisfaction)
│   └── algorithm.rs     # Main orchestration loop
└── tests/
    ├── ground_truth.rs      # Known capacity values
    ├── axioms.rs            # Scaling, translation, reflection
    ├── witness_validation.rs # Constraint satisfaction of results
    ├── enumeration.rs       # Naive vs graph-pruned agreement
    └── edge_cases.rs        # Numerical edge cases, error handling
```

**Change from spec:** Added `symplectic.rs` for cleaner separation of symplectic geometry primitives.
Added `verify.rs` for dedicated result verification logic. Split enumerate into submodule.

---

## 2. Dependencies

```toml
[package]
name = "hk2017"
version = "0.1.0"
edition.workspace = true
license.workspace = true
authors.workspace = true

[dependencies]
nalgebra = "0.33"       # Linear algebra (updated from spec's 0.32)
itertools = "0.13"      # Permutation generation (updated from spec's 0.12)
thiserror = "1.0"       # Error derive macros

[dev-dependencies]
approx = "0.5"          # Float comparison in tests
```

**Note:** No dependencies on other workspace crates. This crate is standalone.

---

## 3. Critical Design Decisions

### 3.1 Interior-Only Critical Point Limitation

**Decision:** Follow the MATLAB reference implementation exactly.

**Behavior:**
- Solve KKT for interior critical point
- Reject permutations where any β_i < 0
- If ALL permutations are rejected, return an explicit error

**Documentation:** The limitation is documented in:
1. Module-level doc comment in `lib.rs`
2. `Hk2017Result::interior_only_assumption` field (always `true`)
3. Error variant `Hk2017Error::NoFeasibleInteriorPoint` with diagnostic info

**Verification:** We cannot check if we missed a boundary maximum. This is an
uncheckable assumption. The result struct explicitly flags this.

### 3.2 Enumeration Strategies

**Decision:** Implement both naive and graph-pruned enumeration.

```rust
pub enum EnumerationStrategy {
    /// Enumerate all subset permutations: O(F!)
    Naive,
    /// Enumerate cycles in facet transition graph
    GraphPruned,
}
```

**KNOWN LIMITATION: Graph Pruning May Miss Optimal Solutions**

During implementation, we discovered that graph-pruned enumeration is **too
aggressive** for some polytopes, including the tesseract.

The issue: The HK2017 formula maximizes Q over *all orderings* of facets,
not just orderings that correspond to physically valid Reeb flow transitions.
The Simple Orbits Theorem guarantees that the optimal Q value corresponds to
a valid physical orbit, but the *ordering* that achieves this maximum may not
follow direct transition edges.

For the tesseract, the naive algorithm finds optimal permutation [0, 2, 5, 1, 4, 6],
which involves 6 facets. The transitions 0→2 and other consecutive pairs in this
sequence do NOT have valid Reeb flow edges (⟨p_i, n_j⟩ ≤ 0). Yet this ordering
achieves Q = 0.125, giving capacity = 4.0.

**Recommendation:** Use naive enumeration for correctness. Graph pruning tests
are marked `#[ignore]` until the pruning strategy is improved.

**TODO:** Improve graph pruning to consider multi-step transitions or implement
a smarter pruning strategy based on closure constraint feasibility.

### 3.3 Numerical Tolerances

```rust
/// Tolerance for floating-point equality checks
pub const EPS: f64 = 1e-12;

/// Tolerance for constraint satisfaction (height sum, closure)
pub const CONSTRAINT_TOL: f64 = 1e-10;

/// Tolerance for checking β ≥ 0 (reject if β < -POSITIVE_TOL)
pub const POSITIVE_TOL: f64 = 1e-10;

/// Tolerance for Lagrangian face detection (ω ≈ 0)
pub const LAGRANGIAN_TOL: f64 = 1e-8;
```

**Rationale:**
- `EPS` is for exact arithmetic comparisons (capacity formula)
- `CONSTRAINT_TOL` is looser to account for numerical error in solving
- `POSITIVE_TOL` matches `CONSTRAINT_TOL` for consistency
- `LAGRANGIAN_TOL` is looser because Lagrangian detection is a coarse classification

### 3.4 Verification Strategy

**Decision:** Always verify in debug builds; optional in release.

```rust
impl Hk2017Result {
    /// Verify all constraints are satisfied. Panics on violation in debug builds.
    pub fn verify(&self, facet_data: &FacetData) {
        if cfg!(debug_assertions) {
            self.verify_impl(facet_data).expect("Result verification failed");
        }
    }

    /// Explicit verification that returns Result
    pub fn verify_checked(&self, facet_data: &FacetData) -> Result<(), VerificationError> {
        self.verify_impl(facet_data)
    }
}
```

In the main algorithm, `verify()` is called on every result before returning.

---

## 4. Data Flow

```
Input: PolytopeHRep { normals, heights }
         │
         ▼
    ┌─────────────┐
    │  validate   │  Check: lengths match, normals unit, heights > 0
    └─────────────┘
         │
         ▼
    ┌─────────────┐
    │ preprocess  │  Compute: FacetData { omega_matrix, reeb_vectors, ... }
    └─────────────┘
         │
         ▼
    ┌─────────────┐
    │  enumerate  │  Generate permutations (naive or graph-pruned)
    └─────────────┘
         │
         ▼ (for each permutation σ)
    ┌─────────────┐
    │   solve     │  Build KKT system, solve, check β ≥ 0
    └─────────────┘
         │
         ▼
    ┌─────────────┐
    │   track     │  Update q_max if Q(σ, β) > q_max
    └─────────────┘
         │
         ▼
    ┌─────────────┐
    │   verify    │  Check constraints satisfied (debug builds)
    └─────────────┘
         │
         ▼
Output: Hk2017Result { capacity, optimal_permutation, optimal_beta, ... }
```

---

## 5. Error Handling

```rust
#[derive(Debug, thiserror::Error)]
pub enum Hk2017Error {
    #[error("Invalid polytope: {0}")]
    InvalidPolytope(String),

    #[error("No permutation yielded a feasible interior critical point ({checked} checked, {rejected} rejected)")]
    NoFeasibleInteriorPoint {
        checked: usize,
        rejected: usize,
        /// Why permutations were rejected
        rejection_reasons: RejectionHistogram,
    },

    #[error("All permutations have non-positive Q value")]
    NoPositiveQ,

    #[error("KKT system is singular for permutation {permutation:?}")]
    SingularKkt { permutation: Vec<usize> },

    #[error("Numerical instability: {0}")]
    NumericalInstability(String),
}

/// Histogram of rejection reasons for diagnostic purposes
#[derive(Debug, Default)]
pub struct RejectionHistogram {
    pub negative_beta: usize,
    pub singular_kkt: usize,
    pub non_positive_q: usize,
}
```

**Philosophy:** Errors should be informative enough to diagnose why the algorithm failed.

---

## 6. Test Plan

### 6.1 Ground Truth Tests

| Polytope | Expected c_EHZ | Source | Facets |
|----------|---------------|--------|--------|
| Tesseract [-1,1]⁴ | 4.0 | HK2017 Ex 4.6 | 8 |
| Rectangle [0,2]×[0,1] × [0,2]×[0,1] | 2.0 | Product formula | 8 |
| Rectangle [0,2]×[0,1] × [0,1]×[0,1] | 1.0 | Product formula | 8 |
| Rectangle [0,1]×[0,1] × [0,1]×[0,1] | 1.0 | Product formula | 8 |
| Scaled tesseract [-2,2]⁴ | 16.0 | Scaling axiom | 8 |

### 6.2 Property Tests (No Known Value Required)

| Property | Test Description |
|----------|-----------------|
| **Witness closure** | Σ β_i n_i = 0 within CONSTRAINT_TOL |
| **Witness height** | Σ β_i h_i = 1 within CONSTRAINT_TOL |
| **Witness positivity** | β_i ≥ -POSITIVE_TOL for all i |
| **Action = capacity** | Computed action of witness = returned capacity |
| **Q formula** | capacity = 1/(2 * q_max) exactly |
| **Scaling** | c(λK) = λ² c(K) for λ ∈ {0.5, 2.0, 3.7} |
| **Translation** | c(K + v) = c(K) for random v |
| **Reflection** | c(-K) = c(K) |
| **Enumeration agreement** | Naive and GraphPruned yield same capacity |
| **Capacity positive** | c > 0 for all valid polytopes |
| **Monotonicity** | K ⊆ L ⟹ c(K) ≤ c(L) (for nested polytopes) |

### 6.3 Edge Case Tests

| Case | Expected Behavior |
|------|-------------------|
| Minimum facets (2) | Should work (degenerate but valid) |
| Origin on boundary | Error: heights not all positive |
| Non-unit normals | Error or normalize (TBD - spec says unit required) |
| Duplicate normals | Error: redundant facets |
| Nearly parallel normals | Should work, may have numerical issues |
| All ω_ij = 0 (Lagrangian) | All permutations have Q = 0, error |

### 6.4 Regression Tests

Any polytope that exposes a bug during development becomes a permanent test case.

---

## 7. FFI Integration

The FFI crate (`rust_viterbo_ffi`) will be updated separately to expose:

```rust
#[pyfunction]
fn hk2017_capacity_hrep(
    normals: Vec<[f64; 4]>,
    heights: Vec<f64>,
    use_graph_pruning: bool,
) -> PyResult<Hk2017ResultPy> { ... }
```

**Note:** The existing `hk2019_capacity_hrep` stub will be replaced. The name uses
"hk2017" to match the paper's arXiv date (December 2017), not the GAFA publication
date (2019).

---

## 8. Open Questions (Resolved)

| Question | Resolution |
|----------|------------|
| Boundary maxima handling | Follow MATLAB: interior only, document limitation |
| Graph pruning | Implement both naive and graph-pruned |
| FFI function naming | Use `hk2017_capacity_hrep` (matches paper) |
| Verification frequency | Always in debug, optional in release |
| Tolerances | Hardcoded sensible defaults per spec |

---

## 9. Implementation Order

1. **types.rs** - Data structures and error types
2. **symplectic.rs** - J matrix, ω, Reeb vectors
3. **preprocess.rs** - FacetData computation
4. **enumerate/naive.rs** - Subset permutation enumeration
5. **solve.rs** - KKT solver
6. **verify.rs** - Constraint verification
7. **algorithm.rs** - Main loop (naive only initially)
8. **lib.rs** - Public API
9. **tests/** - Ground truth and property tests
10. **enumerate/graph.rs** - Graph-pruned enumeration
11. **FFI integration** - Update ffi crate

---

## 10. Assumptions That Cannot Be Checked

**CRITICAL WARNING FOR FUTURE AGENTS:**

The following assumption is made by this implementation and CANNOT be verified:

> **Assumption:** For the polytopes being computed, the global maximum of Q(σ, β)
> over M(K) occurs at an interior point (all β_i > 0), not on the boundary.

If this assumption is violated:
- The algorithm will still return a result
- The result will be **INCORRECT** (capacity too large)
- There is **NO WAY** to detect this from the output

**Indicators that the assumption MAY be violated:**
- High rejection rate (many permutations have β_i < 0)
- Polytope has many Lagrangian faces
- Result seems anomalously large compared to similar polytopes

**Mitigation:**
- Cross-validate with independent methods when available
- Test against known ground truth values
- Be suspicious of results for "unusual" polytopes
