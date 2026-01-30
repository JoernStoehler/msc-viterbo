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

The `profile_workload` binary enables flamegraph profiling:

```bash
cd packages/rust_viterbo
cargo build --release -p tube --bin profile_workload
cargo flamegraph --bin profile_workload -o flamegraph.svg
```

Profiling results should be documented here after manual analysis.

## Escalation Procedures

- If HK2017 R² drops below 0.95: Check for numerical instability in permutation evaluation
- If Tube results change significantly: Verify no Lagrangian 2-faces in test fixtures
- If runtime increases unexpectedly: Profile and check for algorithmic regressions

## Changelog

- 2026-01-30: Initial implementation and findings
