---
name: debugging-numerical
description: Numerical debugging and tolerance handling. Tolerance constants, floating-point comparison patterns, and debugging numerical issues. Use when dealing with precision, tolerances, NaN, or floating-point comparisons.
---

[proposed]

# Numerical Debugging

Guidance for debugging numerical issues and understanding tolerance handling in rust_viterbo.

## Tolerance Constants

### geom2d (`geom2d/src/tolerances.rs`)

| Constant | Value | Purpose |
|----------|-------|---------|
| `EPS` | `1e-10` | General floating-point comparison |
| `EPS_VERTEX` | `1e-9` | Vertex coincidence detection |
| `EPS_AREA` | `1e-12` | Area positivity check |
| `MAX_COORD` | `1e15` | Overflow prevention |

### geom4d (`geom4d/src/tolerances.rs`)

| Constant | Value | Purpose |
|----------|-------|---------|
| `EPS` | `1e-10` | General floating-point comparison |
| `EPS_UNIT` | `1e-9` | Unit vector validation (‖n‖ ≈ 1) |
| `EPS_HEIGHT` | `1e-12` | Height positivity check (h > 0) |
| `MAX_COORD` | `1e15` | Overflow prevention |

## Critical Design Principle

When checking `value > 0`, use `value > EPS_*` (not `>= EPS_*`) so that values exactly at the tolerance are rejected as ambiguous.

## Common Pitfalls

### 1. Direct Float Equality
**Never** use `==` for floats. Use:
```rust
use approx::assert_relative_eq;
assert_relative_eq!(computed, expected, epsilon = 1e-10);
```

### 2. Forgetting to Validate LP Solutions
After any LP solver call, verify the solution satisfies constraints:
```rust
let residual = (A * solution - b).norm();
assert!(residual < EPS, "LP solution violates constraints");
```

### 3. SVD Rank Detection
Use tolerance when counting significant singular values:
```rust
let rank = svd.singular_values.iter().filter(|&&s| s > EPS).count();
```

### 4. Coordinate Validity
Always check for:
- NaN: `!coord.is_finite()`
- Infinity: `!coord.is_finite()`
- Overflow: `coord.abs() > MAX_COORD`

## Debugging Patterns

### debug_assert! for Invariants
```rust
debug_assert!(normals.iter().all(|n| (n.norm() - 1.0).abs() < EPS_UNIT));
```
Only runs in debug builds—no release overhead.

### Structured Error Messages
Include tolerance values:
```rust
#[error("distance {distance:.2e} < {EPS_VERTEX:.2e}")]
```

### Test Categories
- **Positive**: Valid inputs accepted
- **Negative**: Each error variant triggered
- **Edge cases**: Near-tolerance values
- **Property tests**: Scaling, translation invariance

## Validation Order

Validate in order of increasing cost:
1. Count checks (O(1))
2. Coordinate validity (O(n))
3. Geometric properties (O(n))
4. Pairwise checks (O(n²))
5. LP/optimization (expensive)

## Tolerance Philosophy

- Tolerances are **informed guesses** for numerical error accumulation
- Be **permissive during search**, strict at final validation
- Document reasoning for each tolerance value
- When debugging: temporarily tighten tolerances to find where precision is lost
