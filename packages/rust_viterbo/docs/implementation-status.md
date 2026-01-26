# Implementation Status

## Current Status (2026-01-26)

A new tube algorithm implementation has been created following [developer-spec-v2.md](developer-spec-v2.md).

### Tube Crate (`packages/rust_viterbo/tube/`)

| Component | Status | Notes |
|-----------|--------|-------|
| Symplectic primitives | ✅ Done | J, K matrices, ω form |
| H-rep polytope | ✅ Done | Input validation |
| 2-face enumeration | ⚠️ Partial | Checks all pairs, not just adjacent |
| Trivialization (τ, τ⁻¹) | ✅ Done | Quaternion basis |
| Transition matrices | ✅ Done | det ≠ 1 issue noted |
| Tube data structure | ✅ Done | Affine maps, action functions |
| Tube extension | ✅ Done | Flow map computation |
| Fixed point finding | ✅ Done | Closure detection |
| 4D reconstruction | ✅ Done | With validation |
| Branch-and-bound | ✅ Done | With pruning |
| FFI bindings | ✅ Done | tube_capacity_hrep |

### Known Limitations

1. **2-face enumeration**: Currently checks ALL facet pairs, not just geometrically adjacent ones. This causes false positives for Lagrangian 2-face detection. Proper implementation requires vertex enumeration.

2. **Transition matrix determinant**: The spec claims det(ψ) = 1 (symplectic), but testing shows det ≠ 1 for general normal pairs. This may be a spec issue or additional conditions not captured.

3. **Placeholder polygons**: 2-face polygons are placeholders (unit squares). Need proper vertex enumeration to compute actual 2-face vertices.

### Tests

34 tests passing:
- Geometry: 12 tests (J/K matrices, symplectic form, polygon ops)
- Polytope: 7 tests (H-rep validation, Reeb vectors, 2-face detection)
- Trivialization: 7 tests (roundtrip, basis, transition)
- Tube: 6 tests (affine maps, closure detection)
- Algorithm: 2 tests (Lagrangian rejection, cross-polytope)

---

# Archived Code Audit (v0.1.0)

> **⚠️ ARCHIVED CODE** — This section describes the v0.1.0 implementation which was deleted.
> The code is preserved at git tag `v0.1.0-archive`.

Status of the archived rust_viterbo crate implementation.

This document tracks what was verified in the old implementation. May be useful for understanding past issues.

## Status Legend
- ❌ Not done
- 🔄 In progress
- ✅ Done
- ⏳ Blocked

## CRITICAL DEPENDENCY: optim crate ⏳

The `optim` crate (`packages/rust_viterbo/optim/`) is a **STUB** that needs implementation.

**What's blocked on it:**
- `hk2019.rs::solve_qp_for_permutation` - currently uses incomplete vertex+edge enumeration
- Tests pass "by luck" because test case optima happen to be at vertices/edges

**Implementation plan:** See `optim/SPEC.md`

**DO NOT** waste time trying to fix the HK2019 QP solver without first implementing the optim crate.

---

## Test Coverage Summary (2026-01-20)
- Total tests: 186 (153 algorithm + 33 geom) + 4 optim
- Ignored: 6 (known issues or blocked tests)

---

## Debug Audit Summary (2026-01-20)

This section documents where the mathematical writeups, implementations, and tests have issues.

### 1. HK2019 Algorithm ❌ INCOMPLETE

| Category | Issue | Status |
|----------|-------|--------|
| **Math writeup** | Formula correct: Q(σ,β) = Σ_{j<i} β_{σ(i)} β_{σ(j)} ω(n_{σ(i)}, n_{σ(j)}) | ✅ OK |
| **Math writeup** | c_EHZ = (1/2) × [max Q]^{-1} — correct | ✅ OK |
| **Implementation** | `compute_q` — correctly implements formula | ✅ OK |
| **Implementation** | `solve_qp_for_permutation` — vertex + edge enumeration | ❌ INCOMPLETE |
| **Implementation** | For tesseract: Q=0.125 found correctly | ⚠️ Works by luck |
| **Test** | `tesseract_qp_solver_finds_optimal` — passes | ⚠️ Happens to pass |
| **Test** | `billiard_hk2019_agreement` — <0.1% relative error | ⚠️ Empirical only |

**Problem Analysis (2026-01-20):**

The HK2017 paper gives TWO equivalent formulations:

**Formulation 1 (Theorem 1):**
- Maximize Q(σ,β) subject to β ≥ 0, Σβ_i h_i = 1, Σβ_i n_i = 0
- Q is INDEFINITE quadratic, constraints are LINEAR
- This is indefinite QP over a polytope

**Formulation 2 (Remark 1.4):**
- Minimize (Σβ_i h_i)² subject to β ≥ 0, Σβ_i n_i = 0, Q(β) = 1
- Objective is CONVEX, but Q=1 is QUADRATIC EQUALITY constraint
- This is QCQP (Quadratically Constrained QP)

**BOTH formulations are NON-CONVEX:**
1. F1: indefinite objective → non-convex
2. F2: quadratic equality Q=1 → non-convex (hyperboloid constraint)

**Why the current implementation is wrong:**

The vertex + edge enumeration only checks 0D (vertices) and 1D (edges) faces. For a 3D feasible region (tesseract), the optimum could be on a **2D face** - which we don't check.

The tests pass because the optima for test cases happen to be at vertices or edges. This is **luck**, not correctness.

**To fix properly:** Need a global optimization solver. See `optim/SPEC.md` for the implementation plan. **DO NOT** attempt to fix the QP solver without first implementing the optim crate.

### 2. Billiard (LP) Algorithm

| Category | Issue | Severity |
|----------|-------|----------|
| **Math writeup** | Epigraph LP reformulation — rigorous, textbook technique | ✅ OK |
| **Math writeup** | Rudolf 2022 theorems correctly cited (3-bounce bound) | ✅ OK |
| **Implementation** | LP formulation correct, uses minilp | ✅ OK |
| **Implementation** | Capacity computation verified: tesseract=4, triangle×triangle=1.5 | ✅ OK |
| **Implementation** | **Witness segment_times are zeros** (placeholder) | ⚠️ Incomplete |
| **Implementation** | Index convention (LP edge vs polygon facet) — **documented but tricky** | ⚠️ Fragile |
| **Test gap** | `billiard_witness_closes` is **ignored** (witness doesn't close) | ⚠️ Acknowledged |
| **Test gap** | `billiard_witness_positive_segment_times` is **ignored** | ⚠️ Acknowledged |
| **Test gap** | No test that validates witness satisfies differential inclusion | ❌ Missing |

**Root cause for witness issues**: The billiard trajectory gives correct T-length but doesn't directly map to Reeb orbit dynamics. Converting to a Reeb witness requires solving flow equations (see spec Section 5.1). Previous formulas were bogus (335% error) and removed.

### 3. Tube Algorithm

| Category | Issue | Severity |
|----------|-------|----------|
| **Math writeup** | Flow map formula t(p) = h_k(h_j - ⟨n_j,p⟩)/(2ω(n_k,n_j)) — correct | ✅ OK |
| **Math writeup** | Rotation additivity in Sp̃(2) — correct | ✅ OK |
| **Math writeup** | Trivialization τ_F — verified in unit tests | ✅ OK |
| **Implementation** | `compute_flow_map` — appears correct | ⚠️ Unverified E2E |
| **Implementation** | `reconstruct_4d_from_2d` — uses barycentric coords, may have edge cases | ⚠️ Fragile |
| **Implementation** | `solve_closed_tube` — skips empty polygon check in closure mode | ⚠️ Risky |
| **Test gap** | No end-to-end test with known capacity result | ❌ Missing |
| **Test gap** | No test comparing tube algorithm to billiard/HK2019 | ❌ Missing |

**Investigation (2026-01-20)**: Tested tube algorithm on multiple polytopes:
- Tesseract: NoValidOrbits (Lagrangian product, as expected)
- Generic polytope (tesseract+1 facet): NoValidOrbits (rotations 1.25, 1.50)
- Cross-polytope (16-cell): NoValidOrbits (rotations ~1.8)
- 24-cell: NoValidOrbits (rotations 0.5-0.7)

All closure candidates have rotation ≠ 1.0. This suggests either:
1. These polytopes don't have short periodic orbits of the required type
2. The rotation accumulation may have an error
3. The CH2021 paper uses specially constructed polytopes

**Status**: Algorithm runs but finding a polytope with valid orbits requires more investigation.

### 4. Cross-Algorithm Agreement ✅ IMPROVED

| Test | Status | Notes |
|------|--------|-------|
| Billiard vs HK2019 on tesseract | ✅ Both=4.0 | HK2019 QP fixed |
| Billiard vs HK2019 on random products | ✅ <1% error | 3 proptests passing |
| Billiard vs HK2019 on triangle×triangle | ⚠️ Slow | HK2019 with 6!=720 perms takes ~0.1s |
| Tube vs Billiard on tesseract | ❌ N/A | Tube returns NoValidOrbits (Lagrangian degeneracy) |
| All three on non-Lagrangian polytope | ❌ Missing | Need non-Lagrangian polytope with known capacity |

### 5. Specification Gaps

| Spec | Gap | Impact |
|------|-----|--------|
| algorithm-hk2019-spec.md | No analytical solution for QP | Must implement numerical QP |
| algorithm-billiard-spec.md | Witness construction incomplete (§8.5) | Documented limitation |
| tube-geometry-spec.md | "Prove claims in Section 4" TODO | Claims used without proof |
| algorithm-spec.md | No explicit complexity analysis | Performance unclear |

---

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

## CRITICAL: HK2019 QP Solver (hk2019.rs) ❌ INCOMPLETE

The HK2019 algorithm requires solving a **non-convex optimization problem** (see Section 1 above).

**History:**
- Grid search: replaced with vertex enumeration
- Vertex enumeration: passes tests but is mathematically incomplete

**Why vertex enumeration is incomplete:**

The claim "for quadratic maximization over a polytope, the optimum is at a vertex" is **FALSE** for indefinite quadratics. The maximum can be at vertices, edges, 2D faces, or higher-dimensional faces.

The current code only checks vertices (0D) and edges (1D). For the tesseract (3D feasible region), the optimum could be on a 2D face.

| Function | Issue | Status |
|----------|-------|--------|
| `solve_qp_for_permutation` | Vertex + edge enumeration | ❌ Incomplete |
| `compute_q` | Verified against known optimal | ✅ Tested |
| `enumerate_subsets` | Enumerates BFS vertices | ✅ Works |

**Tests pass by luck**, not correctness:
- `tesseract_optimal_q_value`: Q=0.125 ✓ (optimum happens to be at a vertex)
- `billiard_hk2019_agreement`: <1% error (doesn't prove correctness)

**To fix:** Need QCQP solver or global optimizer (SCIP, Gurobi, etc.)

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

**Tests**: 17

**Removed (2026-01-20)**: The following functions and tests were deleted because `find_minimal_billiard` used a WRONG algorithm (vertex-search only, misses edge-interior optima):
- `find_minimal_billiard` — only checked vertices, but Minkowski billiard optima can be at edge interiors (e.g., triangle×triangle at t=1/3)
- `minimal_billiard_length` — wrapper for the wrong function
- `find_facet_for_vertex`, `find_facet_containing_point`, `find_supporting_vertex`, `find_supporting_facet` — helper functions only used by the deleted functions
- All tests for these functions

The CORRECT algorithm is in `billiard_lp.rs` which uses LP to search over continuous t∈[0,1] parameters along edges.

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
| 2026-01-20 | **Debug Audit Session** | Comprehensive review of all 3 algorithms |
| 2026-01-20 | HK2019 analysis | Confirmed QP grid-search is fundamentally broken |
| 2026-01-20 | Billiard analysis | Capacity correct, witness incomplete but documented |
| 2026-01-20 | Tube analysis | Unit-tested but no E2E verification |
| 2026-01-20 | Test gaps identified | Cross-algorithm agreement tests mostly missing |
| 2026-01-20 | **HK2019 QP fix** | Replaced grid-search with vertex enumeration |
| 2026-01-20 | Algorithm agreement | Billiard↔HK2019 now <1% (was 10%) |
| 2026-01-20 | Tube investigation | Tested on cross-polytope, 24-cell - no valid orbits found |
| 2026-01-20 | Test count | 153 passed, 6 ignored (was 149 passed, 8 ignored) |
