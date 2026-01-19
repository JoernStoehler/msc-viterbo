# Code Audit Tracker

This document tracks invariants that need verification via debug_asserts, unit tests, or code comments.

## Status Legend
- ❌ Not done
- 🔄 In progress
- ✅ Done

## Test Coverage Summary (2026-01-19)
- Total tests: 181 (148 algorithm + 33 geom)
- Ignored: 14 (known issues or blocked tests)

---

## CRITICAL: HK2019 QP Solver (hk2019.rs)

The custom QP solver has a known bug (returns Q=0.119 vs expected 0.125 for tesseract).

| Function | Issue | Status |
|----------|-------|--------|
| `solve_qp_for_permutation` | Custom grid-search, unreliable | ❌ |
| `compute_null_space` | No verification tests | ❌ |
| `project_to_constraints` | No convergence tests | ❌ |
| `compute_q` | No known-answer tests | ❌ |

**Decision (2026-01-19)**: Replace with external QP crate (osqp or clarabel). Custom solver consumed >6h without working.

**Tests**: 9 (but 2 ignored due to the bug)

---

## CRITICAL: Witness Segment Times (billiard.rs)

The `construct_2bounce_witness` and `construct_3bounce_witness` functions compute **approximate** segment times that can be 10-40% off from the true capacity.

| Function | Issue | Status |
|----------|-------|--------|
| `construct_2bounce_witness` | segment_times are approximate | 🔄 Documented |
| `construct_3bounce_witness` | segment_times are approximate | 🔄 Documented |

**Note**: The capacity returned by the LP is CORRECT. Only the witness times are wrong.

**Decision needed**: Either remove misleading segment_times or implement proper Reeb flow times.

---

## HIGH: Polygon Operations (billiard.rs) ✅

| Function | Invariant | Status |
|----------|-----------|--------|
| `from_hrep` | Vertices satisfy constraints | ✅ 3 tests |
| `support` | Returns max over vertices | ✅ 3 tests |
| `supporting_vertex` | Returns correct argmax | ✅ 2 tests |
| `polar` | Correct dual construction | ✅ 3 tests |
| `width_euclidean` | Correct width formula | ✅ 2 tests |
| `find_facet_for_vertex` | Vertex i on facet i | ✅ 1 test |
| `find_facet_containing_point` | Point on returned facet | ✅ 2 tests |
| `find_supporting_vertex` | Correct support | ✅ 1 test |
| `find_supporting_facet` | Normal aligned with direction | ✅ 1 test |
| `find_minimal_billiard` | Returns trajectory with action | ✅ 4 tests |

**Tests**: 27

---

## HIGH: LP Billiard (billiard_lp.rs) ✅

| Function | Invariant | Status |
|----------|-----------|--------|
| `solve_3bounce_lp` | LP models problem correctly | ✅ 2 tests |
| `solve_2bounce_lp` | LP models problem correctly | ✅ 2 tests |
| `is_3bounce_nondegenerate` | Detects coincident bounces | ✅ 1 test |
| `edges_adjacent` | Correct wraparound | ✅ 4 tests |
| `lp_result_to_3bounce_trajectory` | Index mapping correct | ✅ 2 tests |
| `find_supporting_vertex_idx` | Correct vertex | ✅ 2 tests |
| `find_supporting_facet_idx` | Correct facet | ✅ 2 tests |

**Tests**: 16

---

## HIGH: Tube Algorithm (tube.rs) ✅

| Function | Invariant | Status |
|----------|-----------|--------|
| `trivialization` | Projects to span{Jn, Kn} | ✅ 2 tests |
| `inverse_trivialization` | Reconstructs point in plane | ✅ 1 test |
| `barycentric_coords` | Sum to 1, reconstruct point | ✅ 4 tests |
| `compute_flow_map` | Affine map for facet transition | ✅ 2 tests |
| `Tube` state machine | Tracks current/start face correctly | ✅ 2 tests |

**Tests**: 11

---

## MEDIUM: Polygon Clipping (polygon.rs) ✅

| Function | Invariant | Status |
|----------|-----------|--------|
| `intersect` | Correct Sutherland-Hodgman | ✅ 4 tests |
| `minimize` | Returns vertex minimum | ✅ 1 test |
| `clip_polygon_by_edge` | Correct half-plane clip | ✅ 3 tests |
| `signed_area` | CCW positive, CW negative | ✅ 2 tests |
| `centroid` | Interior point | ✅ 2 tests |

**Tests**: 23

---

## MEDIUM: Witness Verification (result.rs) ✅

| Function | Invariant | Status |
|----------|-----------|--------|
| `WitnessOrbit::verify` | Computes verification metrics | ✅ 4 tests |
| `verify_differential_inclusion` | Cone membership check | ✅ 5 tests |
| Billiard witness breakpoints | ⟨n_k, p⟩ = h_k on facet k | ✅ 1 test |
| Billiard witness facet transitions | Adjacent facets share 2-face | ✅ 1 test |
| Billiard witness segment times | All times > 0 | ✅ 1 test |
| Billiard witness closure | γ(T) = γ(0) | ⚠️ 1 ignored (known issue) |

**Tests**: 14 (13 passing, 1 ignored)

---

## MEDIUM: Symplectic (geom/symplectic.rs) ✅

| Function | Invariant | Status |
|----------|-----------|--------|
| `symplectic_form_2d` | ω(Jv, v) = |v|² | ✅ 2 tests |
| `transition_matrix` | Sp(2) matrix | ✅ 4 tests |
| `trivialization` | Preserves ω | ✅ 2 tests |
| `rotation_number` | ρ ∈ [0, 0.5] | ✅ 5 tests |

**Tests**: 33 (in geom crate)

---

## LOW: Affine Maps (affine.rs) ✅

| Function | Invariant | Status |
|----------|-----------|--------|
| `AffineFunc` | Evaluation correct | ✅ 4 tests |
| `AffineMap` | Composition, identity | ✅ 5 tests |

**Tests**: 9

---

## LOW: Polytope Preprocessing (polytope.rs) ✅

| Function | Invariant | Status |
|----------|-----------|--------|
| `get_two_face` | Order-independent lookup | ✅ 1 test |
| `faces_adjacent_to` | Returns all faces with facet | ✅ 1 test |
| `PolytopeData::new` | Filters Lagrangian 2-faces | ✅ 1 test |
| `TwoFaceData::rotation` | ρ ∈ (0, 0.5) | ✅ 1 test |

**Tests**: 4

---

## Remaining Critical Work

1. **HK2019 QP Solver**: Replace with proper library or fix the bug
2. **Witness Segment Times**: Document clearly or implement correctly
3. **Integration Tests**: Add tests verifying literature values match

---

## Completion Log

| Date | Item | Notes |
|------|------|-------|
| 2026-01-19 | billiard.rs | 27 unit tests added |
| 2026-01-19 | billiard_lp.rs | 16 unit tests added |
| 2026-01-19 | tube.rs | 11 unit tests added |
| 2026-01-19 | polygon.rs | 23 unit tests added |
| 2026-01-19 | result.rs | 14 unit tests (13 passing + 1 ignored) |
| 2026-01-19 | polytope.rs | 4 unit tests added |
| 2026-01-19 | Witness action test | Split into ignored test with clear documentation |
| 2026-01-19 | Algorithm output verification | 3 tests verifying billiard witness properties |
