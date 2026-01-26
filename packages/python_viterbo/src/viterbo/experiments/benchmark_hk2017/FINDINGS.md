# HK2017 Benchmark Findings

**Date:** 2026-01-26
**Status:** Complete (updated after bug fix)

## Executive Summary

The HK2017 algorithm scales linearly with permutation count, with approximately **1 microsecond per permutation**. Two enumeration variants are available:

| Variant | Description | Speed |
|---------|-------------|-------|
| **Naive** | Enumerate all ordered subsets | Baseline |
| **GraphPruned** | Only cycles in adjacency graph | 2-7x faster |

Both variants now produce **identical results** after the constraint verification fix.

### Quick Reference

| Facets | Permutations (Naive) | Cycles (GraphPruned) | Naive Time | GraphPruned Time |
|--------|---------------------|----------------------|------------|------------------|
| 5 | 320 | ~84 | ~0.3 ms | ~0.1 ms |
| 8 | 109,592 | ~5,556 | ~110 ms | ~15 ms |
| 9 | 986,400 | ~126k | ~1.3 s | ~0.5 s |
| 10 | 9,864,090 | varies | ~10 s | ~2-5 s |

## Bug Fix: Constraint Verification

During this experiment, we discovered and fixed a critical bug in the HK2017 solver.

### The Problem

The KKT solver could return invalid solutions when the constraint system was over-determined or inconsistent. For example, a 4-facet permutation in R⁴ has:
- 4 variables (β values)
- 5 equality constraints (1 height + 4 closure)

For general-position normals (like a simplex), no solution exists, but the LU solver returned garbage that violated constraints.

### The Symptom

Naive and GraphPruned gave different capacities:
- Simplex (before fix): naive=0.044, graph_pruned=0.089
- Simplex (after fix): both=0.101

### The Fix

Added verification that the solution satisfies constraints after solving:
```rust
let residual = (A * beta - b).norm();
if residual > tolerance {
    return Infeasible(ConstraintViolation);
}
```

### Mathematical Insight

Q **IS** rotation-invariant when the closure constraint Σβᵢnᵢ = 0 is satisfied:
```
ω(Σⱼ≠ₐ βⱼnⱼ, nₐ) = ω(-βₐnₐ, nₐ) = -βₐ·ω(nₐ,nₐ) = 0
```

The apparent non-invariance was due to garbage solutions violating closure.

## Results

### Scaling Model

```
time_ms = 5.51e-04 × permutations^1.059
R² = 0.9997
```

Runtime is essentially **linear in permutation count**.

### Performance Comparison

| Facets | Naive | GraphPruned | Speedup |
|--------|-------|-------------|---------|
| 5 | 0.27 ms | 0.13 ms | 2.0x |
| 8 | 111 ms | 15 ms | **7.4x** |
| 9 | 1383 ms | 551 ms | 2.5x |

GraphPruned is fastest for axis-aligned polytopes (tesseract) where the adjacency graph is sparse.

### Rejection Statistics

With the constraint verification fix, many permutations are correctly rejected:

| Polytope | Evaluated | Rejected | Rejection Rate |
|----------|-----------|----------|----------------|
| Tesseract (8f) | 109,592 | ~100k | ~91% |
| Simplex (5f) | 320 | 260 | 81% |

Most rejections are due to:
1. **ConstraintViolation** - no valid β exists (over-determined system)
2. **NegativeBeta** - interior critical point has β < 0
3. **NonPositiveQ** - Q ≤ 0 (not a maximum)

## Practical Guidance

### Predicting Runtime

Given a polytope with F facets:
1. Compute theoretical permutations: `perms = Σₖ₌₂^F (F! / (F-k)!)`
2. Estimate naive time: `time_ms ≈ perms / 1000`
3. GraphPruned is 2-7x faster depending on polytope structure

### Which Variant to Use?

- **GraphPruned (recommended)**: Faster, same results, safe to use
- **Naive**: Use for validation or if GraphPruned has issues

### Budget Inversion

| Budget | Max Facets (Naive) | Max Facets (GraphPruned) |
|--------|-------------------|-------------------------|
| 1 second | 8 | 9 |
| 5 seconds | 9 | 10 |
| 30 seconds | 10 | 10+ |

### FFI Limitation

The FFI enforces a **10-facet limit** to prevent runaway computation.

## Discoveries

### 1. Facet Count Gaps in 4D

Random convex hulls in R⁴ cannot produce certain facet counts:
- **5 points** → exactly 5 facets (simplex)
- **6 points** → 8 or 9 facets
- **7 points** → 8, 9, 11-14 facets (never 10!)
- **Gap counts:** 6, 7, 10 are impossible with random vertex hulls

### 2. Closure Constraint Feasibility

For a permutation using k facets, the closure constraint Σβᵢnᵢ = 0 with βᵢ ≥ 0 requires zero to be in the conic hull of the k normals. This fails for:
- Small k < 5 on general-position polytopes
- Any k where normals don't "balance out"

Axis-aligned polytopes (tesseract) have opposite normal pairs that easily satisfy closure.

## Files Generated

- `data/benchmark-hk2017/timings.json` — Raw timing data (both algorithms)
- `data/benchmark-hk2017/analysis.json` — Fitted models and statistics
- `config/benchmark-hk2017/default.json` — Config with both algorithms

## Tests Added

Three regression tests prevent future breakage:
1. `test_simplex_naive_and_graph_pruned_agree` — The case that exposed the bug
2. `test_result_satisfies_constraints` — Verifies β ≥ 0, Σβh = 1, Σβn = 0
3. `test_simplex_rejects_infeasible_permutations` — Confirms detection works

## Conclusion

The HK2017 implementation is now correct and well-tested. GraphPruned is recommended for production use due to its 2-7x speedup with identical results.
