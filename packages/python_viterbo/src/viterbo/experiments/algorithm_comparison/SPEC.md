# algorithm-comparison Experiment

**Status:** In Progress

## Research Question

How do the three EHZ capacity algorithms (HK2017, Billiard, Tube) compare in terms of:
1. Agreement on overlapping domains (do they give the same capacity?)
2. Success/failure domains (which polytopes work for which algorithm?)

## Method

### Polytope Selection

**Choices made without systematic evaluation:**
- Fixed test cases were chosen as "first idea accepted" - no comparison of alternatives
- Random polytopes added after user feedback

**Known literature values used for validation:**
| Polytope | Expected Capacity | Source |
|----------|------------------|--------|
| Tesseract [-1,1]^4 | 4.0 | HK2017 Example 4.6 |
| Pentagon × RotatedPentagon(90°) | 2cos(π/10)(1+cos(π/5)) ≈ 3.441 | HK-O 2024 counterexample |

**Polytope categories tested:**
1. Fixed Lagrangian products with known values (validation)
2. Random n-gon × m-gon products (coverage)

**Not tested (potential gaps):**
- Non-Lagrangian polytopes via Tube (HK2017 too slow for >8 facets)
- Systematic parameter sweeps
- Edge cases near algorithm boundaries

### Stages

1. **stage_build**: Generate test polytopes, run HK2017 + Billiard, store results
2. **stage_analyze**: (TODO) Compare capacities, compute statistics
3. **stage_plot**: (TODO) Visualize agreement/disagreement patterns

## Success Criteria

- Document which algorithm pairs agree/disagree
- Identify systematic discrepancies
- Validate against known literature values

## Expected Outputs

- data/algorithm-comparison/results.json
- assets/algorithm-comparison/comparison_table.png

