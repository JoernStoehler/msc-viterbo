# polytope-database

**Priority:** P2
**Milestone:** M1 (Code Correctness)
**Status:** Partial implementation; blocked on FFI

## Goal

Build a central database of polytopes with volumes, capacities, and systolic ratios for data science exploration of Viterbo's conjecture.

## Current State

- **Stage 1 (stage_polytopes.py):** Complete — generates tesseract, simplex, cross-polytope, 24-cell, random polytopes
- **Stage 2 (stage_volume.py):** Stub data — needs `volume_hrep()` FFI
- **Stage 3 (stage_capacity.py):** Stub data — needs capacity FFI

## Blocked by

- `volume_hrep()` FFI not implemented (requires: decide on volume algorithm)
- Capacity FFI not exposed (requires: hk2017 or tube crate completion)

## Acceptance Criteria

1. Each stage runs without errors
2. Invariants hold for all rows at each stage
3. JSON serialization works
4. All tests pass (`pytest tests/test_polytope_database.py`)

## Spec and Code

- SPEC: `experiments/polytope_database/SPEC.md`
- Code: `experiments/polytope_database/`

## Labor Estimate

- **AI labor:** Moderate (implement FFI wrappers, connect stages)
- **Human help:** Low (review FFI design, validate volume formula choice)
