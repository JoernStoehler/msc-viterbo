# runtime_performance_analysis Findings

**Status:** Complete

## Summary

This experiment characterizes the runtime performance of the HK2017 and Tube algorithms for computing EHZ capacity of convex polytopes.

## Key Results

### HK2017 Algorithm

**Scaling behavior:** Runtime scales approximately linearly with permutations evaluated.

- **Formula:** `t_ms ≈ α × perms` where `α ≈ 1.0 µs/permutation`
- **R² > 0.99** for both naive and graph-pruned variants
- **Practical limit:** ~10 facets (FFI enforced due to factorial complexity)

The graph-pruned variant evaluates fewer permutations than naive but has slightly higher per-permutation overhead due to graph traversal.

### Tube Algorithm

**Scaling behavior:** Runtime scales approximately linearly with tubes explored.

- **Formula:** `t_ms ≈ β × tubes` where `β ≈ 1.6 µs/tube`
- **R² ≈ 0.92**
- **Applicable to:** Polytopes without Lagrangian 2-faces

The Tube algorithm can handle larger polytopes (16+ facets) that are impractical for HK2017.

### Algorithm Comparison

For polytopes suitable for both algorithms:

| Algorithm | Applicability | Strength |
|-----------|--------------|----------|
| HK2017 naive | Any polytope ≤10 facets | Simple, predictable |
| HK2017 graph | Sparse facet graphs ≤10 facets | Faster for sparse graphs |
| Tube | Non-Lagrangian polytopes | Handles 16+ facets |

## Artifacts

- `data/runtime-performance-analysis/benchmark_results.json` - Raw timing data
- `data/runtime-performance-analysis/analysis_results.json` - Fitted models
- `assets/runtime-performance-analysis/*.tex` - LaTeX tables
- `assets/runtime-performance-analysis/*.png` - Figures

## Profiling

### Methodology

Profiled using `valgrind --tool=callgrind` (instruction-level profiling).

Note: `cargo flamegraph` requires `perf` with kernel support. In containerized environments
where the kernel version doesn't match available `linux-tools-*` packages, use callgrind instead:

```bash
cd packages/rust_viterbo
cargo build --release -p tube --bin profile_workload
valgrind --tool=callgrind --callgrind-out-file=callgrind.out ./target/release/profile_workload tube_cross
callgrind_annotate callgrind.out --auto=yes
```

### Top-5 Hotspots (Tube Algorithm)

**Cross-polytope workload** (16 facets, 15840 tubes/iteration):

| Rank | Function | % Instructions | Notes |
|------|----------|----------------|-------|
| 1 | `tube::algorithm::tube_capacity` | 23.8% | Core algorithm loop |
| 2 | `tube::geometry::intersect_polygons` | 16.2% | Polygon clipping |
| 3 | `_int_free` (glibc) | 8.8% | Memory deallocation |
| 4 | `__memcpy_avx_unaligned_erms` | 7.3% | Memory copying |
| 5 | `Vec::from_iter` | 7.3% | Vector allocations |

**24-cell workload** (24 facets, 1152 tubes/iteration):

| Rank | Function | % Instructions | Notes |
|------|----------|----------------|-------|
| 1 | `tube::algorithm::tube_capacity` | 32.7% | Core algorithm loop |
| 2 | `nalgebra::linalg::inverse::do_inverse4` | 13.3% | 4×4 matrix inversion |
| 3 | `tube::geometry::intersect_polygons` | 12.5% | Polygon clipping |
| 4 | `Vec::from_iter` | 7.4% | Vector allocations |
| 5 | `tube::preprocess::preprocess` | 6.3% | Vertex enumeration |

### Observations

1. **Core algorithm dominates**: `tube_capacity` + `intersect_polygons` account for 40-45% of runtime
2. **Memory allocation overhead**: malloc/free/realloc combined ~20% — potential optimization target
3. **Matrix operations**: `do_inverse4` more prominent with complex polytopes (24-cell)
4. **Preprocessing cost**: Vertex enumeration is ~6% for 24-cell, amortized over iterations

### Optimization Opportunities

- **High impact**: Reduce allocations in inner loops (reuse buffers)
- **Medium impact**: Optimize polygon intersection (hot path)
- **Low impact**: Precompute matrix inverses where possible

## Escalation Procedures

- If HK2017 R² drops below 0.95: Check for numerical instability in permutation evaluation
- If Tube results change significantly: Verify no Lagrangian 2-faces in test fixtures
- If runtime increases unexpectedly: Profile and check for algorithmic regressions

## Changelog

- 2026-01-30: Added profiling results with top-5 hotspots (callgrind)
- 2026-01-30: Initial implementation and findings
