# Code Audit Tracker

This document tracks invariants that need verification via debug_asserts, unit tests, or code comments.

## Status Legend
- ❌ Not done
- 🔄 In progress
- ✅ Done

## Test Coverage Summary (2026-01-19)
- Total tests: 182 (149 algorithm + 33 geom)
- Ignored: 8 (known issues or blocked tests)

## Test Organization (2026-01-19)

Tests are organized by **topic** (not mechanism) in `src/tests/`:

| File | Lines | Topic |
|------|-------|-------|
| `capacity_known_values.rs` | 26 | Literature-verifiable values (tesseract=4) |
| `capacity_scaling_axiom.rs` | 128 | c(λK) = λ²c(K) |
| `capacity_monotonicity.rs` | 51 | K⊆L ⟹ c(K)≤c(L) |
| `algorithm_agreement.rs` | 125 | Billiard vs HK2019 agreement |
| `algorithm_metadata.rs` | 73 | Algorithm traits and input validation |
| `billiard_witness.rs` | 163 | Witness orbit geometry |
| `lagrangian_product.rs` | 246 | Product detection/structure |
| `polygon_2d.rs` | 107 | 2D polygon operations |
| `tube_algorithm.rs` | 96 | Tube (CH2021) tests |
| `polytope_preprocessing.rs` | 34 | PolytopeData construction |
| `fixtures.rs` | 142 | Test polytopes and random generation |

Plus **unit tests** in each module file (`billiard.rs`, `tube.rs`, `polygon.rs`, etc.)

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

The `construct_2bounce_witness` and `construct_3bounce_witness` functions have **placeholder zeros** for segment_times.

| Function | Issue | Status |
|----------|-------|--------|
| `construct_2bounce_witness` | segment_times = zeros (NOT IMPLEMENTED) | ✅ Documented |
| `construct_3bounce_witness` | segment_times = zeros (NOT IMPLEMENTED) | ✅ Documented |

**Note**: The capacity returned by the LP is CORRECT. Only the witness times are missing.

**Decision (2026-01-19)**: Previous bogus formulas (335% error, no derivation) removed. Now placeholder zeros with clear TODOs.

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
| 2026-01-19 | tube.rs | 11 unit tests added (+ flow direction tests) |
| 2026-01-19 | polygon.rs | 23 unit tests added |
| 2026-01-19 | result.rs | 14 unit tests (13 passing + 1 ignored) |
| 2026-01-19 | polytope.rs | 4 unit tests added |
| 2026-01-19 | Witness action test | Split into ignored test with clear documentation |
| 2026-01-19 | Algorithm output verification | 3 tests verifying billiard witness properties |
| 2026-01-19 | **Test Reorganization (v2)** | Reorganized by TOPIC, not mechanism. 12 files <250 lines each |
| 2026-01-19 | capacity_known_values.rs | Literature-verifiable capacity values |
| 2026-01-19 | capacity_scaling_axiom.rs | c(λK) = λ²c(K) property tests |
| 2026-01-19 | capacity_monotonicity.rs | K⊆L ⟹ c(K)≤c(L) property tests |
| 2026-01-19 | algorithm_agreement.rs | Cross-algorithm agreement tests |
| 2026-01-19 | billiard_witness.rs | Witness geometry verification |
| 2026-01-19 | lagrangian_product.rs | Product detection and structure tests |
| 2026-01-19 | polygon_2d.rs | 2D polygon operations |
| 2026-01-19 | tube_algorithm.rs | Tube (CH2021) algorithm tests |
| 2026-01-19 | Segment times cleanup | Removed bogus formulas, now placeholder zeros |
