# benchmark-hk2017 Experiment

**Status:** Executed

## Research Question

How does HK2017 algorithm runtime scale with polytope parameters? Can we build predictive models for:
1. Given polytope parameters → expected runtime
2. Given time budget → what polytopes are feasible to process

## Background

HK2017 (Haim-Kislev 2017) is currently the only fully-implemented capacity algorithm in this codebase.
It computes EHZ capacity by solving a QP for each permutation of facets.

**Current FFI state:**
- Only **Naive enumeration** is exposed (GraphPruned has known issues and is disabled)
- The FFI rejects polytopes with >10 facets (hardcoded limit)
- Returns: `capacity`, `permutations_evaluated`, `permutations_rejected`, `optimal_permutation`, `optimal_beta`, `q_max`

**Theoretical complexity:**
- Naive enumeration: O(F!) permutations where F = facet count
- For F facets, total permutations = Σ_{k=2}^F C(F,k) × k! = Σ_{k=2}^F F!/(F-k)!
- Per-permutation: O(k³) for KKT system solve where k = permutation length

| Facets | Total Permutations |
|--------|-------------------|
| 5      | 320               |
| 8      | 109,592           |
| 9      | 986,400           |
| 10     | 9,864,090         |

## Method

### Stage 1: Build (`stage_build.py`)
Generate polytopes and time HK2017 execution.

**Polytope families used:**
1. **Tesseract**: 8 facets (standard test case, capacity = 4.0)
2. **Random simplices**: 5 facets (from 5 random points)
3. **Random convex hulls**: 9 facets (from 6-7 random points)

**Note:** In 4D, random convex hulls have facet count gaps. 6 and 7 facets are impossible; 10 facets is extremely rare (requires 7 points but almost never occurs).

**For each polytope, record:**
- `family`: polytope family name
- `n_facets`: number of facets
- `n_points`: number of points used for generation
- `wall_time_ms`: elapsed wall time in milliseconds
- `capacity`: computed capacity
- `permutations_evaluated`: from result
- `permutations_rejected`: from result
- `success`: whether computation succeeded

### Stage 2: Analyze (`stage_analyze.py`)
Fit scaling models and build prediction formulas.

**Analyses:**
1. Empirical scaling: Plot wall_time vs n_facets
2. Permutation count verification: Compare observed to theoretical
3. Time per permutation: Compute wall_time / permutations_evaluated
4. Prediction model: Linear regression on log(time) ~ log(perms)

### Stage 3: Plot (`stage_plot.py`)
Generate visualizations.

## Success Criteria

| Criterion | Result |
|-----------|--------|
| Data collection completes | ✓ 15/15 runs succeeded |
| Permutation counts match theory | ✓ Exact match |
| Predictive model R² > 0.95 | ✓ R² = 0.9997 |
| Practical guidance produced | ✓ See FINDINGS.md |

## Outputs

- `data/benchmark-hk2017/timings.json` — Raw timing data
- `data/benchmark-hk2017/analysis.json` — Fitted models and statistics
- `data/benchmark-hk2017/plots/` — Visualizations
- `FINDINGS.md` — Detailed findings and practical guidance

## Key Findings

**Scaling model:** `time_ms = 5.51e-04 × perms^1.059` (R² = 0.9997)

**Time per permutation:** ~1.04 µs (mean across all runs)

**Practical guidance:**
- 8 facets: ~110 ms
- 9 facets: ~1.3 s
- 10 facets: ~10-13 s (extrapolated)

See `FINDINGS.md` for complete analysis.

## Limitations

1. **FFI limitation**: Only Naive enumeration tested
2. **10-facet limit**: Cannot benchmark larger polytopes
3. **Facet count gaps**: 6, 7, 10 facets not achievable with random hulls
4. **Machine-dependent**: Absolute timings depend on hardware

## Config Variants

- `default.json`: 10 reps per config, facets [5, 8, 9]
- `quick.json`: 5 reps per config for development
