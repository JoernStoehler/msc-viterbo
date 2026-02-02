# counterexample-hko

## Goal
Produce a self-contained showcase of the Haim-Kislev-Ostrover 2024 counterexample to Viterbo's conjecture, including JSON data and factor projection plots.

## Blocked by
- geom4d H-rep construction and capacity computation
- Orbit construction from scratch (minimum action orbit visiting each facet once)

## Acceptance Criteria
1. JSON output contains all geometric data with correct values
2. Systolic ratio matches known value (sqrt(5)+3)/5 > 1
3. Plot clearly shows the orbit structure in both projections
4. Segments are numbered consistently between panels

## Notes
- Pentagon product K x T: regular pentagon K (circumradius 1) in q-plane, rotated pentagon T (-pi/2) in p-plane
- Outputs: `data/counterexample-hko/hko2024.json`, `assets/counterexample-hko/orbit-projections.png`
- Reference: HK-O 2024 arXiv:2405.16513
