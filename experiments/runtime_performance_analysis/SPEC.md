# runtime_performance_analysis

## Problem

Characterize algorithm runtime to enable:
1. Predicting computation time from polytope properties
2. Identifying optimization opportunities via profiling
3. Choosing the right algorithm for a given workload

This experiment supersedes `benchmark_hk2017` and extends it to cover the Tube algorithm.

## Approach

### Polytope Sources

**Fixed fixtures (construct in Python):**
- `unit_tesseract` (8 facets) — HK2017 only (Lagrangian 2-faces)
- `unit_cross_polytope` (16 facets) — HK2017 + Tube
- `unit_24_cell` (24 facets) — HK2017 + Tube
- `four_simplex` (5 facets) — HK2017 only

Construction is trivial (see `benchmark_hk2017/stage_build.py` for examples). No FFI needed.

**Random polytopes for HK2017:**
- Use existing Python convex hull approach from `benchmark_hk2017`
- Facet counts: 5, 8, 9, 10 (FFI limit)

**Random polytopes for Tube:**
- Requires filtering for non-Lagrangian 2-faces
- Add FFI binding for `random_hrep(n_facets, min_omega, seed) -> Option<(normals, heights)>`
- Facet counts: 8, 10, 12, 14, 16

### Timing Method

Python wall-clock via `time.perf_counter()` around FFI calls:
- 1 warmup iteration (discarded)
- 5 timed iterations per configuration
- Record mean, std, min, max

### Profiling Method

Manual `cargo flamegraph` workflow:
```bash
cargo install flamegraph
cargo flamegraph --bench profile_workload -- --bench
```

Create benchmark binary at `packages/rust_viterbo/benches/profile_workload.rs` with:
1. HK2017 naive on 10-facet polytope
2. HK2017 graph-pruned on 10-facet polytope
3. Tube on 16-facet cross-polytope

### Stages

**stage_build.py:**
1. Construct fixtures in Python
2. Generate random polytopes (Python for HK2017, FFI for Tube)
3. Time each (polytope, algorithm) pair
4. Output: `data/runtime_performance_analysis/benchmark_results.json`

**stage_tabulate.py:**
1. Load benchmark results
2. Generate LaTeX tables: runtime by facets, algorithm comparison, prediction formulas
3. Output: `assets/runtime_performance_analysis/*.tex`

**stage_analyze.py:**
1. Fit scaling models (time vs permutations for HK2017, time vs facets for Tube)
2. Compute R², RMSE
3. Generate figures: scatter plots, residuals, speedup bars
4. Output: `data/runtime_performance_analysis/analysis_results.json`, `assets/runtime_performance_analysis/*.png`

### Analysis

**HK2017:** Fit `time_ms = α × perms^β`. Prior finding: β ≈ 1.059, ~1µs/permutation.

**Tube:** Determine functional form empirically. Candidate: `time_ms = f(facets, tubes_explored)`.

## Acceptance Criteria

- [ ] FFI binding added: `random_hrep(n_facets, min_omega, seed)`
- [ ] Benchmark binary created: `benches/profile_workload.rs`
- [ ] stage_build.py collects ≥50 (polytope, algorithm) timing pairs
- [ ] stage_tabulate.py generates 3 LaTeX tables
- [ ] stage_analyze.py fits models with R² > 0.9 for HK2017
- [ ] Flamegraphs generated and top-5 hotspots documented in FINDINGS.md
- [ ] FINDINGS.md includes prediction formula per algorithm

## Files to Modify

**New files:**
- `packages/python_viterbo/src/viterbo/experiments/runtime_performance_analysis/stage_build.py`
- `packages/python_viterbo/src/viterbo/experiments/runtime_performance_analysis/stage_tabulate.py`
- `packages/python_viterbo/src/viterbo/experiments/runtime_performance_analysis/stage_analyze.py`
- `packages/python_viterbo/src/viterbo/experiments/runtime_performance_analysis/FINDINGS.md`
- `packages/python_viterbo/config/runtime_performance_analysis/default.json`
- `packages/rust_viterbo/benches/profile_workload.rs`

**Modified files:**
- `packages/rust_viterbo/ffi/src/lib.rs` — add `random_hrep` binding

**Output files:**
- `packages/python_viterbo/data/runtime_performance_analysis/benchmark_results.json`
- `packages/python_viterbo/data/runtime_performance_analysis/analysis_results.json`
- `packages/latex_viterbo/assets/runtime_performance_analysis/*.tex` (3 tables)
- `packages/latex_viterbo/assets/runtime_performance_analysis/*.png` (3 figures)
- `packages/latex_viterbo/assets/runtime_performance_analysis/flamegraph_*.svg` (2 flamegraphs)

## Open Questions

None. All decisions resolved:
- Fixtures: construct in Python (simple, already done in benchmark_hk2017)
- Random Tube polytopes: add FFI binding (requires Rust `preprocess()` for validation)
- Profiling: manual workflow with cargo-flamegraph (documented in FINDINGS.md)
