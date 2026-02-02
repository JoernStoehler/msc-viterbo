# counterexample-hko

**Status:** Blocked
**Blocked by:** Verified EHZ capacity computation (hk2017 crate or tube crate)

## Goal

Produce a self-contained, illustrative showcase of the Haim-Kislev-Ostrover 2024 counterexample to Viterbo's conjecture.

## Research Question

Demonstrate that the pentagon product K x T has systolic ratio > 1, violating Viterbo's conjecture. This is a P1 priority for the thesis as a foundational validation target.

## What Exists

**Location:** `experiments/counterexample_hko/`

**Implemented files:**
- `SPEC.md` - Complete specification with method, success criteria, and expected outputs
- `__init__.py` - Module docstring
- `stage_build.py` - Builds geometric data from scratch:
  - Pentagon construction (K in q-plane, T in p-plane rotated -pi/2)
  - H-representation generation (normals + heights)
  - Closed-form capacity/volume/systolic ratio (uses known formulas, not computed)
  - Minimum action orbit construction (2-bounce T-billiard algorithm)
  - JSON output with numerical values and LaTeX exact expressions
- `stage_plot.py` - Creates two-panel factor projection plot:
  - Left panel: K factor (q-plane)
  - Right panel: T factor (p-plane)
  - Numbered orbit segments with arrows

**Current approach:** Uses closed-form expressions from HK-O 2024 paper rather than computing capacity algorithmically.

## What's Blocking

1. **Verified capacity algorithm** - The current implementation uses the closed-form formula from the paper (`c = 2*cos(pi/10)*(1 + cos(pi/5))`). For thesis completeness, we should:
   - Validate this against computed capacity from hk2017 or tube algorithm
   - This requires either crate to be functional and exposed via FFI

2. **Orbit correctness verification** - The `build_minimum_orbit()` function constructs the 2-bounce T-billiard trajectory geometrically, but:
   - Needs verification against the paper's description
   - Should match what the capacity algorithm would produce as the optimal orbit

## When Unblocked

1. Implement hk2017 crate with FFI exposure (or tube crate as alternative)
2. Add test: computed capacity matches closed-form value within tolerance
3. Verify orbit from algorithm matches manually constructed orbit
4. Run full pipeline: `stage_build.py` then `stage_plot.py`
5. Review generated outputs against paper figures

## Learnings from Previous Attempt

- Pentagon product construction is straightforward (product of 2D polygons)
- The T-billiard orbit structure is well-documented in HK-O 2024
- Closed-form formula serves as excellent ground truth for algorithm validation
- Factor projection plots effectively visualize 4D orbits
- Segment numbering between panels helps understand alternating K/T structure

## Success Criteria

1. JSON output contains all geometric data with correct values
2. Systolic ratio matches known value `(sqrt(5)+3)/5 > 1` (approximately 1.047)
3. Plot clearly shows the orbit structure in both projections
4. Segments are numbered consistently between panels
5. **Validation:** Computed capacity from Rust algorithm matches closed-form within 1e-6
