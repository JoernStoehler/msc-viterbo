# algorithm-comparison Experiment

**Status:** In Progress

## Research Question

How do the three EHZ capacity algorithms (HK2017, Billiard, Tube) compare in terms of:
1. Agreement on overlapping domains (do they give the same capacity?)
2. Success/failure domains (which polytopes work for which algorithm?)

## Method

1. **stage_build**: Generate test polytopes, run all applicable algorithms, store results
   - Lagrangian products (squares, rectangles, triangles, pentagons): HK2017 + Billiard
   - Non-Lagrangian polytopes (cross-polytope, 24-cell): HK2017 + Tube (where tractable)

2. **stage_analyze**: Compare capacities, compute statistics, identify discrepancies

3. **stage_plot**: Visualize agreement/disagreement patterns

## Success Criteria

- Document which algorithm pairs agree/disagree
- Identify any systematic discrepancies (like the triangle×triangle 2× factor)
- Provide trust assessment for each algorithm

## Expected Outputs

- data/algorithm-comparison/results.json
- assets/algorithm-comparison/comparison_table.png
