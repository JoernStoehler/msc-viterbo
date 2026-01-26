# counterexample-hko Experiment

**Status:** Specified

## Research Question

Produce a self-contained, illustrative showcase of the Haim-Kislev-Ostrover 2024 counterexample to Viterbo's conjecture.

## Method

1. **Build**: Compute the pentagon product K x T geometry from scratch:
   - Regular pentagon K in the q-plane (circumradius 1)
   - Rotated regular pentagon T in the p-plane (rotated by -pi/2)
   - Generate H-rep (outward unit normals + heights)
   - Compute capacity, volume, and systolic ratio from closed forms
   - Construct the minimum action orbit (simple orbit visiting each facet once)
   - Output JSON with numerical values and `*_exact` LaTeX strings

2. **Plot**: Create a factor projection plot:
   - Left panel: projection onto q-plane (K)
   - Right panel: projection onto p-plane (T)
   - Show the minimum action orbit with numbered segments
   - Each segment is a line in one factor and a point in the other (alternating)

## Success Criteria

1. JSON output contains all geometric data with correct values
2. Systolic ratio matches known value (sqrt(5)+3)/5 > 1
3. Plot clearly shows the orbit structure in both projections
4. Segments are numbered consistently between panels

## Expected Outputs

- `data/counterexample-hko/hko2024.json` — Full geometric data
- `assets/counterexample-hko/orbit-projections.png` — Factor projection plot
