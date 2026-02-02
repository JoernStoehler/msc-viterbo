# Profiling Hotspots Learnings

**Source:** `packages/python_viterbo/src/viterbo/experiments/runtime_performance_analysis/FINDINGS.md`

## Tube Algorithm Scaling

```
t_ms = beta * tubes, where beta ~ 1.6 us/tube
R^2 ~ 0.92
```

Linear scaling with tube count, slightly less predictable than HK2017.

## Profiling Methodology

```bash
cd packages/rust_viterbo
cargo build --release -p tube --bin profile_workload
valgrind --tool=callgrind --callgrind-out-file=callgrind.out \
  ./target/release/profile_workload tube_cross
callgrind_annotate callgrind.out --auto=yes
```

Note: `cargo flamegraph` requires kernel-matched `perf`. Callgrind works in containers.

## Cross-Polytope Hotspots (16 facets, 15840 tubes/iter)

| Rank | Function | % | Category |
|------|----------|---|----------|
| 1 | `tube::algorithm::tube_capacity` | 23.8% | Algorithm |
| 2 | `tube::geometry::intersect_polygons` | 16.2% | Geometry |
| 3 | `_int_free` (glibc) | 8.8% | Memory |
| 4 | `__memcpy_avx_unaligned_erms` | 7.3% | Memory |
| 5 | `Vec::from_iter` | 7.3% | Allocation |

**Pattern:** Core algorithm (40%) + Memory operations (23%).

## 24-Cell Hotspots (24 facets, 1152 tubes/iter)

| Rank | Function | % | Category |
|------|----------|---|----------|
| 1 | `tube::algorithm::tube_capacity` | 32.7% | Algorithm |
| 2 | `nalgebra::linalg::inverse::do_inverse4` | 13.3% | Linear algebra |
| 3 | `tube::geometry::intersect_polygons` | 12.5% | Geometry |
| 4 | `Vec::from_iter` | 7.4% | Allocation |
| 5 | `tube::preprocess::preprocess` | 6.3% | Setup |

**Pattern:** Core algorithm (45%) + Matrix ops more prominent on complex polytopes.

## Summary by Category

| Category | Cross-Polytope | 24-Cell |
|----------|---------------|---------|
| Core algorithm | ~40% | ~45% |
| Memory (malloc/free/copy) | ~23% | ~15% |
| Linear algebra | <5% | ~13% |
| Preprocessing | <3% | ~6% |

## Optimization Opportunities

### High Impact: Reduce Inner Loop Allocations

Memory operations (malloc/free/memcpy/Vec::from_iter) account for ~20% combined.

**Approach:** Reuse buffers across loop iterations instead of allocating fresh vectors.

### Medium Impact: Optimize Polygon Intersection

`intersect_polygons` is 12-16% of runtime across workloads.

**Approaches:**
- Sutherland-Hodgman optimization for convex polygons
- Early-exit when intersection is empty
- SIMD for vertex operations

### Low Impact: Precompute Matrix Inverses

`do_inverse4` is 13% on 24-cell but <5% on cross-polytope.

Only worth optimizing if focusing on complex polytopes.

## Workload Characteristics

| Polytope | Facets | Tubes/Iter | Profile |
|----------|--------|------------|---------|
| Cross-polytope | 16 | 15,840 | Memory-bound |
| 24-cell | 24 | 1,152 | Compute-bound |

Cross-polytope has many small tubes (memory churn). 24-cell has fewer, larger computations per tube.

## HK2017 vs Tube Performance Model

| Algorithm | Formula | Per-Unit Cost | Notes |
|-----------|---------|---------------|-------|
| HK2017 | t = alpha * perms | ~1.0 us/perm | R^2 > 0.99 |
| Tube | t = beta * tubes | ~1.6 us/tube | R^2 ~ 0.92 |

HK2017 is more predictable but hits factorial wall earlier.

## When to Profile Again

- After refactoring hot functions
- When adding new polytope types
- If runtime regresses unexpectedly
- Before thesis performance claims
