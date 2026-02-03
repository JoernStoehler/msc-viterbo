# polytope-database

**Status:** Blocked
**Blocked by:** FFI missing `volume_hrep()` function

## Goal

Build a central database of polytopes for probing Viterbo's conjecture using data science methods.

## Research Question

Systematically compute capacity, volume, and systolic ratio for a variety of polytope families to identify patterns and potential counterexamples.

## What Exists

**Location:** `experiments/polytope_database/`

**Implemented stages:**
- `stage_polytopes.py` - Generates H-representations for tesseract, simplex, cross-polytope, 24-cell, random polytopes
- `stage_volume.py` - Stub implementation (uses fake volumes)
- `stage_capacity.py` - Stub implementation (uses fake capacities)

**Schema defined:**
- Stage 1: id, family, facet_count, normals, heights, has_lagrangian_2face, is_lagrangian_product
- Stage 2: + volume
- Stage 3: + capacity, systolic_ratio, orbit_breakpoints, orbit_breaktimes, orbit_facet_sequence

## What's Blocking

1. **`volume_hrep()` FFI** - Need to expose 4D volume computation from Rust
2. **Orbit data from Tube** - `TubeResult` doesn't expose breakpoints, only capacity

## When Unblocked

1. Add `volume_hrep(normals, heights) -> float` to FFI
2. Extend `TubeResult` to include `optimal_orbit.breakpoints` (optional)
3. Replace stub implementations with real FFI calls
4. Run pipeline and validate invariants

## Learnings from Previous Attempt

- Staged pipeline design works well (polytopes → volumes → capacities)
- JSON schema with invariants is good for validation
- Consider Parquet for large datasets (JSON is slow)

## Success Criteria

1. Each stage runs without errors
2. All invariants hold (normals unit, heights positive, ratios computed correctly)
3. Database includes ≥50 polytopes across all families
