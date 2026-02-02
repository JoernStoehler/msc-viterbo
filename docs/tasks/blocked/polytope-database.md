# polytope-database

## Goal
Build a central database of polytopes with volumes, capacities, and systolic ratios for data science exploration of Viterbo's conjecture.

## Blocked by
- `volume_hrep()` FFI not implemented (Stage 2)
- `systolic_ratio()` FFI helper not exposed (Stage 3)
- Stages 2-3 use stub data

## Acceptance Criteria
1. Each stage runs without errors
2. Invariants hold for all rows at each stage
3. JSON serialization works
4. All tests pass (`pytest tests/test_polytope_database.py`)

## Notes
- Stage 1 complete: generates tesseract, simplex, cross-polytope, 24-cell, random polytopes
- Schema includes normals, heights, lagrangian flags, volume, capacity, systolic_ratio, orbit data
- Future: convert JSON to Parquet for large datasets
- `stage_build.py` contains legacy monolithic implementation
