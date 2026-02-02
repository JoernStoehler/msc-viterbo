# algorithm-comparison

**Priority:** P2
**Milestone:** M1 (Code Correctness)
**Status:** Partially implemented; blocked on algorithm crates

## Goal

Compare EHZ capacity algorithms (HK2017, Billiard, Tube) for agreement and success domains across polytope families.

## Blocked by

- **hk2017 crate:** Not yet implemented (needs geom4d Characteristic)
- **tube crate:** Not yet implemented (needs geom4d TwoFace, geom2d intersection)
- **billiard crate:** Not yet implemented (needs geom2d trajectory)
- **FFI exposure:** Non-Lagrangian fixtures (cross-polytope, 24-cell, random H-rep)

## Known Issues to Investigate

1. **Triangle × triangle discrepancy:** Billiard=3.0, HK2017=1.5 (factor of 2 error?)
2. **HK2017 vs Tube domain overlap:** 0 overlap in 1000 random 8-facet polytopes (expected?)
3. **24-cell capacity:** Not found in literature; compute and document

## Acceptance Criteria

1. **Agreement table:** For each polytope family, which algorithm pairs agree within tolerance
2. **Systematic discrepancies:** Defined as >5% deviation or wrong sign; identify root cause
3. **Literature validation:** Match known values ±0.1%:
   - Tesseract: 4.0
   - Cross-polytope: 1.0
   - Pentagon product: ~3.441

## Spec and Code

- SPEC: `experiments/algorithm_comparison/SPEC.md`
- Code: `experiments/algorithm_comparison/`

## Labor Estimate

- **AI labor:** High (run experiments, analyze results, debug discrepancies)
- **Human help:** Medium (interpret discrepancies, decide if algorithm bugs or expected behavior)
