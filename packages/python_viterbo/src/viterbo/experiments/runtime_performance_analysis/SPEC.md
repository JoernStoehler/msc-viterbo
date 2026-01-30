# runtime_performance_analysis Experiment

**Status:** Specified

## Research Questions

1. **Scaling:** How does algorithm runtime scale with polytope properties (facet count, vertex count, etc.)?
2. **Hotspots:** Where are the computational hotspots for relevant workloads?
3. **Prediction:** Can we predict runtime from polytope features? What formula works best per algorithm variant?

## Background

This experiment consolidates and extends the findings from `benchmark_hk2017`:

| Prior Finding (benchmark_hk2017) | Status |
|----------------------------------|--------|
| Scaling: time_ms ≈ perms / 1000 | Incorporate |
| Time per permutation: ~1µs | Verify across more polytopes |
| GraphPruned 2-7x faster than Naive | Extend to more cases |
| 10-facet FFI limit for HK2017 | Note as constraint |

**New scope:** Add Tube algorithm, expand facet range, generate profiling data.

## Method

### Polytope Generation

**Fixed fixtures** (via Rust FFI, add bindings as needed):
| Name | Facets | Algorithms | Notes |
|------|--------|------------|-------|
| unit_tesseract | 8 | HK2017 only | Lagrangian 2-faces |
| unit_cross_polytope | 16 | HK2017, Tube | No Lagrangian 2-faces |
| unit_24_cell | 24 | HK2017, Tube | No Lagrangian 2-faces |
| four_simplex | 5 | HK2017 only | Lagrangian 2-faces |

**Random polytopes:**
| Method | Facet counts | Algorithms | Notes |
|--------|--------------|------------|-------|
| Python convex hull | 5, 8, 9, 10 | HK2017 | Existing approach from benchmark_hk2017 |
| Rust `random_hrep` | 8, 10, 12, 14, 16 | Tube | Filtered for no Lagrangian 2-faces |

**Implementation:** Generate in Python, call FFI. The Rust `random_hrep` function is not currently exposed via FFI—add a binding or generate polytopes with the same algorithm in Python.

**Decision rationale:**
- Python generation works for HK2017 (any polytope with 0 ∈ int K)
- Rust `random_hrep` already filters for non-Lagrangian 2-faces (required for Tube)
- If Python reimplementation of `random_hrep` is complex, add FFI binding instead

### Timing Method

Use Python wall-clock timing around FFI calls:

```python
import time

start = time.perf_counter()
result = ffi.hk2017_capacity_hrep(normals, heights, use_graph_pruning)
elapsed_ms = (time.perf_counter() - start) * 1000
```

**Warmup:** Run 1-2 warmup iterations before timing to avoid JIT/cache effects.

**Repetitions:** 5-10 runs per configuration for statistical stability.

### Profiling Method

Use `cargo flamegraph` to profile Rust code:

```bash
cd packages/rust_viterbo
# Install if needed
cargo install flamegraph

# Profile HK2017 on a specific polytope (via test binary)
cargo flamegraph --test hk2017_tests -- test_name_here

# Or profile via a custom benchmark binary (create if needed)
cargo flamegraph --bin benchmark_runner
```

**Workloads to profile:**
1. HK2017 naive on 10-facet random polytope
2. HK2017 graph-pruned on 10-facet random polytope
3. Tube on 16-facet cross-polytope
4. Tube on 16-facet random polytope

**Output:** Flamegraph SVGs showing % time in each function.

### Stages

#### stage_build.py

1. Load/generate polytopes:
   - Fixed fixtures via FFI
   - Random polytopes via Python or FFI
2. For each (polytope, algorithm) pair:
   - Warmup: 1 iteration (discarded)
   - Timing: 5 iterations, record wall-clock ms
   - Record: polytope metadata, timing stats, result metadata
3. Save to `data/runtime_performance_analysis/benchmark_results.json`

**Schema:**
```json
{
  "polytope": {
    "name": "cross_polytope" | "random_hrep_seed_42",
    "facets": 16,
    "vertices": 8,
    "has_lagrangian_2faces": false
  },
  "algorithm": "hk2017_naive" | "hk2017_graph_pruned" | "tube",
  "timing": {
    "mean_ms": 123.4,
    "std_ms": 5.6,
    "min_ms": 118.0,
    "max_ms": 132.0,
    "n_runs": 5
  },
  "result": {
    "capacity": 1.0,
    "permutations_evaluated": 12345,  // HK2017 only
    "tubes_explored": 567             // Tube only
  }
}
```

#### stage_tabulate.py

Generate thesis-ready tables:

1. **Runtime by facet count table** (`runtime_by_facets.tex`)
   - Columns: Facets, HK2017-Naive, HK2017-Graph, Tube
   - Rows: 5, 8, 10, 12, 14, 16 facets (N/A where not applicable)

2. **Algorithm comparison table** (`algorithm_comparison.tex`)
   - Speedup ratios (GraphPruned / Naive, Tube / HK2017)
   - Per-polytope breakdown for fixtures

3. **Prediction formula summary** (`prediction_formulas.tex`)
   - Formula per algorithm variant
   - R² and RMSE values

#### stage_analyze.py

1. **Fit scaling models:**
   - HK2017: time vs permutation count (expect linear)
   - Tube: time vs facets, time vs tubes_explored

2. **Build prediction formulas:**
   - HK2017: `time_ms = α × perms^β` (validate β ≈ 1)
   - Tube: `time_ms = f(facets)` (determine functional form)

3. **Compute fit quality:**
   - R², RMSE, prediction error on held-out set (if enough data)

4. **Generate figures:**
   - `runtime_vs_facets.png` — scatter + fitted curves
   - `prediction_error.png` — residual plot
   - `algorithm_speedup.png` — bar chart of speedup ratios

5. Save analysis to `data/runtime_performance_analysis/analysis_results.json`

### Profiling Workflow (Manual)

Profiling requires manual invocation outside the Python stages:

1. **Install flamegraph:**
   ```bash
   cargo install flamegraph
   # Linux: may need perf permissions
   echo -1 | sudo tee /proc/sys/kernel/perf_event_paranoid
   ```

2. **Create benchmark binary** (if not exists):
   Create `packages/rust_viterbo/hk2017/benches/profile_workload.rs` with representative workloads.

3. **Run profiling:**
   ```bash
   cd packages/rust_viterbo
   cargo flamegraph --bench profile_workload -- --bench
   # Output: flamegraph.svg
   ```

4. **Document hotspots:**
   - Copy SVG to `latex_viterbo/assets/runtime_performance_analysis/`
   - Write top-5 hotspots with % time to FINDINGS.md

## Success Criteria

| Criterion | Measurement |
|-----------|-------------|
| Benchmark data collected | ≥50 polytope/algorithm pairs with timing |
| HK2017 scaling confirmed | R² > 0.95 for time vs permutations |
| Tube scaling characterized | Functional form identified with R² > 0.8 |
| Prediction formulas documented | One formula per algorithm in FINDINGS.md |
| Profiling hotspots documented | Top-5 hotspots with % time |
| Tables generated | All .tex files in assets/ |
| Figures generated | All .png files in assets/ |

## Expected Outputs

### Data Files
- `data/runtime_performance_analysis/benchmark_results.json` — Raw timing data
- `data/runtime_performance_analysis/analysis_results.json` — Fitted models and statistics

### Thesis Assets
- `packages/latex_viterbo/assets/runtime_performance_analysis/runtime_by_facets.tex`
- `packages/latex_viterbo/assets/runtime_performance_analysis/algorithm_comparison.tex`
- `packages/latex_viterbo/assets/runtime_performance_analysis/prediction_formulas.tex`
- `packages/latex_viterbo/assets/runtime_performance_analysis/runtime_vs_facets.png`
- `packages/latex_viterbo/assets/runtime_performance_analysis/prediction_error.png`
- `packages/latex_viterbo/assets/runtime_performance_analysis/algorithm_speedup.png`
- `packages/latex_viterbo/assets/runtime_performance_analysis/flamegraph_hk2017.svg`
- `packages/latex_viterbo/assets/runtime_performance_analysis/flamegraph_tube.svg`

### Documentation
- `FINDINGS.md` — Updated with results, prediction formulas, hotspot analysis

## Config Files

`config/runtime_performance_analysis/default.json`:
```json
{
  "seed": 42,
  "warmup_iterations": 1,
  "timing_iterations": 5,
  "hk2017_facet_counts": [5, 8, 9, 10],
  "tube_facet_counts": [8, 10, 12, 14, 16],
  "random_polytopes_per_facet_count": 10,
  "min_omega": 0.01,
  "output_dir": "data/runtime_performance_analysis"
}
```

## Constraints and Limitations

1. **HK2017 10-facet limit:** FFI rejects >10 facets. Tube has no such limit.
2. **Random polytope rejection:** Rust `random_hrep` rejects ~90% of seeds (unbounded, near-Lagrangian). Budget more seeds accordingly.
3. **Machine-dependent timings:** Absolute values depend on hardware. Focus on relative comparisons and scaling exponents.
4. **Profiling requires sudo/perf:** `cargo flamegraph` needs kernel permissions on Linux.

## Open Questions

1. **FFI for Rust fixtures:** Should we expose `unit_cross_polytope()` etc. via FFI, or construct them in Python? (Recommendation: add FFI bindings for consistency)

2. **Random polytope generation:** Reimplement `random_hrep` in Python, or add FFI binding? (Recommendation: add FFI binding to avoid reimplementation bugs)

3. **Tube algorithm performance variability:** Is Tube runtime predictable from facet count alone, or do other geometric properties matter? (Answer empirically)

## References

- `benchmark_hk2017` experiment (superseded)
- `docs/specs/appendix-experiments-spec.md` sections 5-6
- `docs/conventions/python-experiments.md`
- Rust algorithm docs: `docs/conventions/rust-algorithms.md`
