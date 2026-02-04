---
name: capacity-algorithms
description: EHZ capacity algorithms (HK2017, Tube, Billiard). When to use each, runtime characteristics, applicability domains.
---

# Capacity Algorithms

This skill covers the three EHZ capacity algorithms available in rust_viterbo: HK2017, Tube, and Billiard. Use this to decide which algorithm to apply and understand performance characteristics.

## Quick Reference

| Algorithm | Domain | Complexity | Practical Limit | Status |
|-----------|--------|------------|-----------------|--------|
| HK2017 (naive) | Any polytope | O(F!) | F <= 8 | Unimplemented |
| HK2017 (graph-pruned) | Any polytope | unknown | F <= 10 | Unimplemented |
| Tube | No Lagrangian 2-face | unknown | unknown | Unimplemented |
| Billiard | Lagrangian product | O(E^6) | unknown | Unimplemented |

Where F = number of facets, E = number of edges.

## HK2017 Performance (LEGACY VERSION)

### Runtime Formula

```
time_ms = 5.51e-04 * permutations^1.059
```

Simplified: ~1 microsecond per permutation (linear scaling), R^2 = 0.9997.

### Permutation Count

For F facets: `perms = sum_{k=2}^{F} F!/(F-k)!`

Example: F=5 gives 20 + 60 + 120 + 120 = 320 permutations.

### Budget Inversion

| Budget | Max Facets (Naive) | Max Facets (GraphPruned) |
|--------|-------------------|-------------------------|
| 1 second | 8 | 9 |
| 5 seconds | 9 | 10 |
| 30 seconds | 10 | 10+ |

FFI enforces a **10-facet hard limit** to prevent runaway computation.

### GraphPruned vs Naive

GraphPruned enumerates only cycles in the facet adjacency graph instead of all ordered subsets.

| Facets | Naive Time | GraphPruned Time | Speedup |
|--------|------------|------------------|---------|
| 5 | 0.27 ms | 0.13 ms | 2.0x |
| 8 | 111 ms | 15 ms | 7.4x |
| 9 | 1383 ms | 551 ms | 2.5x |

Best speedup on axis-aligned polytopes (tesseract) where adjacency graph is sparse.

## Tube Algorithm Performance (LEGACY VERSION)

### Runtime Formula

```
t_ms = beta * tubes, where beta ~ 1.6 us/tube
```

R^2 ~ 0.92 (less predictable than HK2017).

### When Applicable

Tube algorithm requires the polytope to be **non-Lagrangian** (no Lagrangian 2-faces).

| Polytope | Tube Time | HK2017 Status |
|----------|-----------|---------------|
| Cross-polytope (16f) | 1.2s | Infeasible |
| 24-cell (24f) | 249ms | Infeasible |

## Reference Capacity Values (LEGACY VERSION)

| Polytope | Facets | Capacity | Algorithm |
|----------|--------|----------|-----------|
| 4-simplex | 5 | 0.4167 | HK2017 |
| Tesseract | 8 | 4.0 | HK2017 |
| Cross-polytope | 16 | 1.0 | Tube |
| 24-cell | 24 | 2.0 | Tube |

## Mahler Bound (MISSING SOURCE)

The Mahler inequality states: `c(K) * c(K^polar) >= 4`.

### Saturating Pairs

1. **Tesseract x Cross-polytope** (polar duals):
   - c(tesseract) = 4.0, c(cross-polytope) = 1.0
   - Product = 4.0 (exact saturation)

2. **24-cell** (self-dual):
   - c(24-cell) = 2.0, c^2 = 4.0 (exact saturation)

These polytopes are extremal for Mahler in 4D.

## Profiling Hotspots (LEGACY VERSION)

### Cross-Polytope (16 facets, 15840 tubes/iter)

| Function | % | Category |
|----------|---|----------|
| tube_capacity | 23.8% | Algorithm |
| intersect_polygons | 16.2% | Geometry |
| Memory ops (malloc/free/memcpy) | ~23% | Memory |

Profile: Memory-bound (many small tubes).

### 24-Cell (24 facets, 1152 tubes/iter)

| Function | % | Category |
|----------|---|----------|
| tube_capacity | 32.7% | Algorithm |
| do_inverse4 | 13.3% | Linear algebra |
| intersect_polygons | 12.5% | Geometry |

Profile: Compute-bound (fewer, larger computations).

## Closure Constraint Feasibility (LEGACY VERSION)

For a k-facet permutation, closure requires: `sum_i beta_i * n_i = 0, beta_i >= 0`

### Failure Modes

1. **Small k < 5** on general-position polytopes: Over-determined
2. **Normals don't balance**: Zero not in conic hull

### Why Axis-Aligned Polytopes are Easier

Tesseract normals come in opposite pairs (+e_j, -e_j). For any facet sequence, there's likely a "balancing" normal available.

## Escalation Triggers (LEGACY VERSION)

1. **Need HK2017 on F > 8**: Consider parallel computation or accept Tube-only
2. **Capacity values change**: Rerun algorithm_inventory and compare
3. **New polytope fails validation**: Check Lagrangian 2-face detection

## Source

Performance data extracted from legacy experiments: `benchmark_hk2017`, `algorithm_inventory`, `runtime_performance_analysis`.

Note: Algorithm crates (hk2017, tube, billiard) are currently stubs awaiting reimplementation. Experiment code exists but cannot run until algorithms are complete.
