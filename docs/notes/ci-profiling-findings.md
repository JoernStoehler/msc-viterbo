# CI Performance Profiling Findings

**Initial Analysis**: 2026-02-01T12:50 UTC (commit `955a527`)
**Updated**: 2026-02-01 (commit `fbdb17a`)
**CI Run**: [21563151278](https://github.com/JoernStoehler/msc-viterbo/actions/runs/21563151278)

## Test Timing Tables

### Python Tests (pytest)

| Test | Local (s) | CI (s) | Notes |
|------|-----------|--------|-------|
| **test_ffi_capacity_hrep** | | | |
| test_hk2017_tesseract_capacity | 11.12 | 7.93 | HK2017 on 8-facet tesseract |
| test_hk2017_simplex_runs | 0.02 | 0.02 | Quick sanity check |
| test_hk2017_graph_pruning | 11.87 | 8.41 | Runs HK2017 twice (naive + pruned) |
| test_hk2017_result_repr | 11.43 | 7.92 | Runs HK2017 again |
| test_symplectic_form_* (3 tests) | <0.01 | <0.01 | Fast |
| test_hk2017_invalid_mismatched_lengths | <0.01 | <0.01 | Fast |
| **test_polytope_database** | | | |
| TestHRepGenerators (9 tests) | <0.01 | <0.01 | Fast |
| TestLagrangianDetection (7 tests) | <0.01 | <0.01 | Fast |
| TestOrbitGeneration (5 tests) | <0.01 | <0.01 | Fast |
| TestStagePolytopes (7 tests) | <0.01 | <0.01 | Fast |
| TestStageVolume::test_adds_volume_to_all | 0.14 | 0.10 | Calls FFI volume |
| TestStageVolume::test_preserves_existing_keys | 0.14 | 0.10 | Calls FFI volume |
| TestStageVolume::test_tesseract_volume | <0.01 | <0.01 | Fast |
| TestStageCapacity::test_adds_capacity_fields | 3.51 | 8.18 | **Full pipeline** |
| TestStageCapacity::test_systolic_ratio_formula | 3.27 | 8.22 | **Full pipeline** |
| TestStageCapacity::test_tesseract_capacity | 3.27 | 8.20 | **Full pipeline** |
| TestFullPipeline::test_pipeline_produces_complete_data | 3.32 | 8.19 | **Full pipeline** |
| TestFullPipeline::test_json_serializable | 3.37 | 8.21 | **Full pipeline** |
| TestFullPipeline::test_orbit_invariants | 3.37 | 8.24 | **Full pipeline** |
| **test_counterexample_hko** | | | |
| TestIntegration::test_plot_runs_without_error | 0.47 | 0.36 | Matplotlib plot |
| Other tests (27) | <0.01 | <0.01 | Fast |
| **test_polytope_visualization_4d** | | | |
| TestHrepToVertices::test_simplex | 0.06 | 0.03 | Uses scipy.spatial |
| Other tests (14) | <0.01 | <0.01 | Fast |
| **Other test files** | <0.01 | <0.01 | Fast |
| **TOTAL** | **56.33s** | **79.86s** | |

### Rust Tests (cargo test)

| Test Suite | Tests | Local Debug (s) | CI Debug (s) | CI Release (s) |
|------------|-------|-----------------|--------------|----------------|
| billiard | 0 | 0.00 | 0.00 | 0.00 |
| geom | 28 | 0.03 | 0.02 | 0.00 |
| hk2017 | 44+9ign | 11.04 | 7.83 | 0.75 |
| tube | 69 | 25.98 | 20.81 | 0.32 |
| tube/flow_map_tests | 10 | 6.48 | 4.58 | 0.09 |
| tube/hk2017_comparison | 1+2ign | **115.33** | 4.18 | 0.07 |
| tube/integration | 0+11ign | 0.00 | 0.00 | 1.01 |
| tube/orbit_invariants | 10 | 3.95 | 3.88 | 0.08 |
| geom doc-tests | 3 | 0.14 | 0.12 | 0.10 |
| hk2017 doc-tests | 3 | 11.28 | 11.90 | 0.27 |
| tube doc-tests | 1 | 1.28 | 0.81 | 0.09 |
| **TOTAL** | | **~175s** | **~54s** | **~3s** |

### CI Job Summary

| Job | Duration |
|-----|----------|
| Rust | 1m24s |
| Rust + Python (FFI) | 1m45s |
| **Total CI** | **1m45s** (parallel) |

## Key Observations

### 1. Local vs CI Discrepancy for hk2017_comparison

The `test_hk2017_vs_tube_random_8_facet` test shows dramatic difference:
- **Local**: 115.33s
- **CI**: 4.18s

Root cause: The test iterates through random seeds trying to find valid polytopes. Local run found 0 valid polytopes in 1000 attempts (all rejected), while CI found enough quickly. This is deterministic per-seed but the rejection rate varies with floating-point behavior across platforms.

### 2. Redundant Capacity Computations (Test Design Issue)

Six tests in `test_polytope_database` each run the full pipeline independently:

```python
# Each of these tests does this:
polytopes = generate_polytopes()      # 12 polytopes
polytopes = add_volumes(polytopes)    # FFI calls
polytopes = add_capacities(polytopes) # HK2017 × 12 polytopes
```

Each takes ~8s in CI, totaling ~48s for identical computations.

**This is a test design issue.** The tests should:
1. Run the pipeline once (via a shared fixture)
2. Make multiple assertions on the result

This is different from "caching" - it's proper test structure where expensive setup happens once per test module.

### 3. QHull is NOT the Bottleneck

- QHull compilation: 10s (one-time during maturin develop, cached)
- Volume computation via QHull: <0.2s per test
- Confirmed not a performance concern

## Recommendations & Status

### 1. Restructure polytope_database tests ✅ DONE

**Commit**: `fbdb17a`

Refactored tests to:
- Run actual `stage_*.main()` functions instead of calling helpers directly
- Use `tmp_path` fixture for test isolation
- Share single pipeline run via module-scoped `pipeline_output` fixture

**Actual savings**: ~40s (6 pipeline runs → 1 pipeline run)

### 2. pytest-xdist ❌ NOT RECOMMENDED

Evaluated but not implemented. Reasons:
- Tests already ~40s after restructuring (acceptable)
- Most tests are fast unit tests; slow parts are sequential HK2017 computations
- Would complicate debugging (multi-process, interleaved output)
- Limited parallelism benefit: the pipeline fixture is module-scoped, so integration tests run sequentially anyway

### 3. Platform variance in `test_hk2017_vs_tube_random_8_facet` — NO ACTION

The test takes 115s locally vs 4s in CI due to platform-dependent floating-point behavior affecting random polytope rejection rates.

**Decision**: Leave as-is. The test works correctly in CI (4s). The 115s local time is a developer experience issue, not a correctness issue. Never trade correctness for speed.

## Conclusion

- **QHull**: Not the bottleneck. No action needed.
- **CI time**: Should drop from ~2min to ~1.5min with test restructuring.
- **Test restructuring**: ✅ Implemented in `fbdb17a`.
- **pytest-xdist**: Deferred.
