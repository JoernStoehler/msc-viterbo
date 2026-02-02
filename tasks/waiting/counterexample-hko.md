# counterexample-hko

**Priority:** P1
**Milestone:** M2 (Thesis Draft)
**Status:** Specified, not started

## Goal

Produce a self-contained showcase of the Haim-Kislev-Ostrover 2024 counterexample to Viterbo's conjecture, including JSON data and factor projection plots.

## Mathematical Background

The counterexample is a pentagon product K × T where:
- K: regular pentagon (circumradius 1) in q-plane
- T: rotated pentagon (-π/2) in p-plane

**Systolic ratio formula:** `sys(K) = 4π√(area_K × area_T) / capacity(K × T)`

**Expected value:** `(√5 + 3)/5 ≈ 1.047 > 1` (violates Viterbo's conjecture)

**Reference:** HK-O 2024, arXiv:2405.16513

## Blocked by

- geom4d: HRep construction for product polytopes
- hk2017 or tube: capacity computation
- Minimum action orbit construction (visits each facet once)

## Acceptance Criteria

1. JSON output contains all geometric data with correct values
2. Computed systolic ratio matches `(√5 + 3)/5` within tolerance
3. Plot clearly shows the orbit structure in both projections
4. Segments are numbered consistently between panels

## Spec and Code

- SPEC: `experiments/counterexample_hko/SPEC.md`
- Code: `experiments/counterexample_hko/`
- Outputs: `data/counterexample-hko/`, `assets/counterexample-hko/`

## Labor Estimate

- **AI labor:** Moderate (orbit construction algorithm, coordinate transforms)
- **Human help:** Medium (verify orbit correctness against paper, review plots)
