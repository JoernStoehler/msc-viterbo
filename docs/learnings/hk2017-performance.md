# HK2017 Performance Learnings

**Source:** `packages/python_viterbo/src/viterbo/experiments/benchmark_hk2017/FINDINGS.md`

## Runtime Formula

```
time_ms = 5.51e-04 * permutations^1.059
R^2 = 0.9997
```

Simplified: **~1 microsecond per permutation** (linear scaling).

### Permutation Count Formula

For a polytope with F facets:
```
perms = sum_{k=2}^{F} F!/(F-k)!
```

Example: F=5 gives 20 + 60 + 120 + 120 = 320 permutations.

### Budget Inversion

| Budget | Max Facets (Naive) | Max Facets (GraphPruned) |
|--------|-------------------|-------------------------|
| 1 second | 8 | 9 |
| 5 seconds | 9 | 10 |
| 30 seconds | 10 | 10+ |

FFI enforces a **10-facet hard limit** to prevent runaway computation.

## GraphPruned vs Naive

GraphPruned enumerates only cycles in the facet adjacency graph instead of all ordered subsets.

| Facets | Naive Time | GraphPruned Time | Speedup |
|--------|------------|------------------|---------|
| 5 | 0.27 ms | 0.13 ms | 2.0x |
| 8 | 111 ms | 15 ms | 7.4x |
| 9 | 1383 ms | 551 ms | 2.5x |

**Best speedup** on axis-aligned polytopes (tesseract) where adjacency graph is sparse.
Both variants produce identical results after the constraint verification fix.

## Facet Count Gaps in 4D

Random convex hulls in R^4 cannot produce certain facet counts:

- 5 points -> exactly 5 facets (simplex)
- 6 points -> 8 or 9 facets (never 6 or 7)
- 7 points -> 8, 9, 11-14 facets (never 10)

**Impossible counts from random vertex hulls:** 6, 7, 10 facets.

This affects experiment design when generating random polytopes.

## Closure Constraint Feasibility

For a k-facet permutation, the closure constraint requires:
```
sum_i beta_i * n_i = 0, with beta_i >= 0
```

This requires zero to be in the **conic hull** of the k selected normals.

### Failure modes:

1. **Small k < 5** on general-position polytopes: Over-determined (5 constraints, 4 variables)
2. **Normals don't balance**: Zero not in conic hull regardless of k

### Why axis-aligned polytopes are easier

Tesseract normals come in opposite pairs (+e_j, -e_j). For any facet sequence, there's likely a "balancing" normal available, making closure feasible.

### Rejection Statistics

| Polytope | Evaluated | Rejected | Rate |
|----------|-----------|----------|------|
| Tesseract (8f) | 109,592 | ~100k | 91% |
| Simplex (5f) | 320 | 260 | 81% |

Most rejections: ConstraintViolation > NegativeBeta > NonPositiveQ.

## Historical Bug: Missing Constraint Verification

The KKT solver returned garbage for over-determined systems. Symptoms:
- Naive and GraphPruned gave different capacities
- Simplex: naive=0.044, graph_pruned=0.089 (correct: 0.101)

Fix: Verify solution satisfies constraints after solving.
```rust
let residual = (A * beta - b).norm();
if residual > tolerance { return Infeasible(ConstraintViolation); }
```

**Regression tests added** to prevent recurrence.
