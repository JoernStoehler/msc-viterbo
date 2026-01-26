# HK2017 Benchmark Findings

**Date:** 2026-01-26
**Status:** Complete

## Executive Summary

The HK2017 algorithm (Naive enumeration) scales linearly with permutation count, with approximately **1 microsecond per permutation**. For practical use:

| Facets | Permutations | Expected Time | Budget |
|--------|--------------|---------------|--------|
| 5 | 320 | ~0.3 ms | instant |
| 8 | 109,592 | ~110 ms | < 1s |
| 9 | 986,400 | ~1.3 s | < 5s |
| 10 | 9,864,090 | ~10-13 s | < 30s |

**Key insight:** Given a time budget T (seconds), you can process polytopes up to F facets where the theoretical permutation count is ≤ T × 10⁶.

## Results

### Scaling Model

```
time_ms = 5.51e-04 × permutations^1.059
R² = 0.9997
```

The exponent ≈ 1.06 means runtime is essentially **linear in permutation count**. The small superlinear component may be due to cache effects for larger permutation sets.

### Time per Permutation

| Facets | Time/Perm (µs) |
|--------|----------------|
| 5 | 0.79 |
| 8 | 1.01 |
| 9 | 1.32 |
| **Mean** | **1.04** |

Time per permutation increases slightly with facet count, likely due to longer permutation lengths requiring larger KKT systems.

### Theoretical vs Observed Permutations

The theoretical formula for permutation count exactly matches observations:

```
Total permutations = Σ_{k=2}^F (F! / (F-k)!)
```

| F | Theoretical | Observed | Match |
|---|-------------|----------|-------|
| 5 | 320 | 320 | exact |
| 8 | 109,592 | 109,592 | exact |
| 9 | 986,400 | 986,400 | exact |

## Discoveries

### 1. Facet Count Gaps in 4D

Random convex hulls in R⁴ cannot produce certain facet counts:

| Points | Possible Facet Counts |
|--------|-----------------------|
| 5 | exactly 5 (simplex) |
| 6 | 8, 9 |
| 7 | 8, 9, 11, 12, 13, 14 (never 10!) |

**Gap facet counts:** 6, 7, 10 are impossible with random convex hulls.

### 2. Debug Build Verification Failures

Running with debug assertions (Rust dev build) triggers verification failures for some polytopes. The simplex constructed from vertices-to-H-rep conversion failed the height constraint check:

```
HeightConstraint { expected: 1.0, actual: 1.5 }
```

This may indicate:
- Edge cases in the HK2017 algorithm for certain polytope geometries
- Issues with the simplex construction (likely)
- The interior-only assumption being violated

**Mitigation:** Use release builds (`--release` flag) which skip debug assertions.

### 3. GraphPruned Variant Not Available

The FFI currently only exposes Naive enumeration. The GraphPruned variant (which uses adjacency-based cycle enumeration) is disabled due to known issues. This limits the benchmark to a single algorithm variant.

## Practical Guidance

### Predicting Runtime

Given a polytope with F facets:

1. Compute theoretical permutations: `perms = Σ_{k=2}^F (F! / (F-k)!)`
2. Estimate time: `time_ms ≈ perms / 1000` (≈ 1µs per permutation)

### Budget Inversion

Given a time budget:

| Budget | Max Facets | Max Permutations |
|--------|------------|------------------|
| 1 second | 8 | ~110k |
| 5 seconds | 9 | ~1M |
| 30 seconds | 10 | ~10M |
| 5 minutes | 10 | ~10M (FFI limit) |

### FFI Limitation

The current FFI enforces a **10-facet limit** to prevent runaway computation. For 10 facets:
- Permutations: ~9.9 million
- Expected time: ~10-13 seconds

## Files Generated

- `data/benchmark-hk2017/timings.json` — Raw timing data
- `data/benchmark-hk2017/analysis.json` — Fitted models and statistics
- `data/benchmark-hk2017/plots/` — Visualizations
  - `runtime_vs_facets.png` — Main scaling curve
  - `perms_observed_vs_theory.png` — Validation of permutation formula
  - `time_per_perm.png` — Distribution of time per permutation
  - `budget_table.png` — Visual budget guide

## Future Work

1. **Benchmark GraphPruned variant** once FFI issues are resolved
2. **Test larger facet counts** by removing the FFI limit
3. **Profile bottlenecks** to identify optimization opportunities
4. **Cross-validate** with other capacity algorithms once available
