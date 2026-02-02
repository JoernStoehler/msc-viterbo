# algorithm-comparison

## Goal
Compare EHZ capacity algorithms (HK2017, Billiard, Tube) for agreement and success domains across polytope families.

## Blocked by
- Non-Lagrangian fixture FFI exposure (unit_cross_polytope, unit_24_cell, asymmetric_cross_polytope, random_hrep)
- Triangle x triangle discrepancy unresolved (Billiard=3.0, HK2017=1.5)
- HK2017 vs Tube domain overlap unclear (0 overlap in 1000 random 8-facet polytopes)

## Acceptance Criteria
1. Document which algorithm pairs agree/disagree
2. Identify systematic discrepancies
3. Validate against known literature values (Tesseract=4.0, Pentagon product~3.441, Cross-polytope=1.0)

## Notes
- Stage 1 (stage_build) partially implemented with Lagrangian products
- Need to add non-Lagrangian polytopes via FFI
- Expected capacity of 24-cell undocumented
- HK2017 performance with 16+ facets untested
