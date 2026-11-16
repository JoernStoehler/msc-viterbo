# Optimization Library Spec

## Problem Statement

Maximize a quadratic form over a polytope:

```
maximize   Q(x) = x^T H x
subject to Ax = b        (m equality constraints)
           x >= 0        (n non-negativity constraints)
```

Where:
- H is n×n symmetric (may be indefinite, may have zero diagonal)
- A is m×n, b is m×1
- The feasible region {x : Ax = b, x >= 0} is a polytope (possibly empty)

## Requirements

1. **Correctness**: Find the GLOBAL maximum, not a local maximum
2. **Efficiency**: Must handle n ≤ 10 variables within reasonable time
3. **Dependencies**: Prefer pure Rust; nalgebra already available

## API

```rust
pub fn maximize_quadratic_over_polytope(
    hessian: &DMatrix<f64>,
    eq_matrix: &DMatrix<f64>,
    eq_rhs: &DVector<f64>,
) -> Result<(f64, DVector<f64>), OptimError>;
```

Returns `(max_value, argmax)` where `max_value = Q(argmax)`.

## Verification Test Cases

These test cases use the symplectic capacity problem from HK2017. The Q there is:
- Q(β) = Σ_{j<i} β_i β_j ω(n_i, n_j)
- Constraint: Σ β_i h_i = 1, Σ β_i n_i = 0, β >= 0

**Test 1: Tesseract**
- 8 facets, feasible region is 3-dimensional polytope
- Optimal Q = 0.125 exactly
- Corresponding capacity = 0.5 / 0.125 = 4.0
- This MUST match - it's the primary validation

**Test 2: Triangle × Triangle (Lagrangian product)**
- 6 facets
- Result must match billiard LP algorithm within 0.1%
- Billiard LP is in `rust_viterbo_algorithm::billiard_lp`

**Test 3: Random Lagrangian products (proptest)**
- Generate random polygon pairs
- Result must match billiard LP within 0.1%

## Development Methodology

**TDD is mandatory.** Previous implementations were wrong because tests were written after the fact to match the implementation rather than to verify correctness.

1. Write a test that calls the API with tesseract inputs and asserts Q = 0.125
2. Make the test pass
3. Add property-based tests verifying Q(result) >= Q(vertex) for all vertices
4. Add comparison tests against billiard LP

## Notes for Implementer

- The HK2019 code in `algorithm/src/hk2019.rs` has an INCOMPLETE implementation (vertex + edge enumeration only). Don't copy it.
- The billiard LP algorithm is CORRECT and can be used as ground truth for Lagrangian products.
- Helper functions `is_indefinite`, `is_positive_semidefinite`, `is_negative_semidefinite` are already in lib.rs.
