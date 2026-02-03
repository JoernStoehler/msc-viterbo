# algorithm-comparison

**Status:** Blocked
**Blocked by:** Billiard FFI not implemented; non-Lagrangian fixture FFI missing

## Goal

Compare the three EHZ capacity algorithms (HK2017, Billiard, Tube) to document where they agree/disagree and which polytope domains each handles.

## Research Question

How do the three EHZ capacity algorithms compare in terms of:
1. Agreement on overlapping domains (do they give the same capacity?)
2. Success/failure domains (which polytopes work for which algorithm?)

## What Exists

**Location:** `experiments/algorithm_comparison/`

- `SPEC.md` - Experiment specification with method, polytope choices, and TODO list
- `__init__.py` - Empty package init
- `stage_build.py` - Generates Lagrangian products and runs HK2017. Includes:
  - `PolytopeRecord` dataclass for storing results
  - Fixed test cases: tesseract (lit=4.0), pentagon counterexample (lit=3.441)
  - Random n-gon x m-gon products (20 samples)
  - HK2017 execution via FFI (working)
  - Billiard stub (returns "Not yet implemented")
  - Tube marked N/A for Lagrangian products

## What's Blocking

1. **Billiard FFI** - The billiard algorithm is not exposed via FFI. The `billiard` crate exists but is marked "draft status" in SPEC.
2. **Non-Lagrangian fixture FFI** - SPEC lists fixtures in `tube/src/fixtures.rs` (cross-polytope, 24-cell, asymmetric cross-polytope, random_hrep) that need FFI exposure to test Tube algorithm.
3. **triangle x triangle discrepancy** - Known bug: Billiard=3.0, HK2017=1.5 (2x factor). Root cause not debugged.

## When Unblocked

1. Expose billiard algorithm via FFI (or mark as out-of-scope if billiard crate won't be completed)
2. Add FFI functions for non-Lagrangian fixtures:
   - `unit_cross_polytope() -> (normals, heights)`
   - `unit_24_cell() -> (normals, heights)`
   - `asymmetric_cross_polytope(seed) -> (normals, heights)`
   - `random_hrep(n_facets, min_omega, seed) -> Option<(normals, heights)>`
3. Add `NonLagrangianRecord` dataclass to stage_build.py
4. Run HK2017 + Tube on non-Lagrangian polytopes
5. Implement stage_analyze and stage_plot
6. Debug triangle x triangle discrepancy

## Learnings from Previous Attempt

1. **triangle x triangle discrepancy** - Billiard=3.0, HK2017=1.5 (2x factor). Not debugged. May indicate a normalization issue or genuine algorithm disagreement.
2. **HK2017 vs Tube disjoint domains** - Earlier Rust exploration found 0 overlap in 1000 random 8-facet polytopes. The algorithms appear to handle fundamentally different polytope classes.
3. **Missing literature values** - Expected capacity of 24-cell is not documented in fixtures.
4. **HK2017 scalability unknown** - Whether HK2017 can handle 16-facet cross-polytope in reasonable time (even with GraphPruning) needs empirical testing.

## Success Criteria

1. Document which algorithm pairs agree/disagree on overlapping domains
2. Identify systematic discrepancies (like the 2x factor for triangle x triangle)
3. Validate against known literature values (tesseract=4.0, pentagon counterexample~=3.441, cross-polytope=1.0)
4. Generate comparison table visualization
