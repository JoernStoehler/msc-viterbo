# Tube Crate Improvements

**Status:** blocked
**Priority:** P3
**Blocked by:** Focus on correctness validation first; improvements are nice-to-have

**Date:** 2026-02-01
**Source:** Comprehensive evaluation of tube crate

## Executive Summary

The tube crate is well-structured with good mathematical documentation, but has accumulated complexity in `algorithm.rs` (1100 lines). Key improvement areas:

1. **Critical bugs/issues**: `p_start` not being refined (flagged as suspicious), shear case untested
2. **Dead code**: 13 items including `omega_matrix`, `deduplicate_vertices`, `symplectic_form_2d`
3. **Naming**: `apply_quat_i` serves dual role (quaternion i vs symplectic J) - needs separate functions
4. **Complexity**: `algorithm.rs` should be split into 4-5 submodules
5. **Type safety**: Missing newtypes for indices, rotation numbers, action values
6. **Test gaps**: Shear case (98 lines of complex math) has zero test coverage

---

## Flagged Issues (Require Jorn's Input)

### p_start Not Refined (algorithm.rs:233-236)
```rust
// For now, we keep p_start unchanged (conservative: may include invalid starts)
```
**Status**: Flagged as suspicious. Unclear why this is "conservative" or if it affects correctness.

### Rotation Accumulation Proof Missing
The code does `tube.rotation + exit_2face.rotation` (algorithm.rs:244). Mathematical justification needs to be written up:
- Infinitesimal case -> integral for smooth -> limit for polytopes (discrete sum)

### apply_quat_i Dual Role
`apply_quat_i` is used for both:
- Quaternionic multiplication by i (quaternion.rs)
- Symplectic J matrix application (symplectic_form, reeb_vector)

**Action needed**: Create two functions with different names:
```rust
pub fn symplectic_j(v: &Vector4<f64>) -> Vector4<f64>  // Symplectic geometry
pub fn quaternion_i(v: &Vector4<f64>) -> Vector4<f64>  // Quaternion multiplication
```

---

## Prioritized Recommendations

### Immediate (Bug Fixes)
1. Investigate `p_start` not being refined
2. Fix 4-simplex test to be strict
3. Add tests for shear case

### Short-Term (Code Quality)
4. Create separate `symplectic_j()` function
5. Remove dead code (13 items)
6. Fix `FlowDirection` enum variant naming (ItoJ -> IToJ)
7. Add `.expect()` context to safe unwraps

### Medium-Term (Refactoring)
8. Split `algorithm.rs` into submodules
9. Decompose complex functions (find_fixed_point_on_line, etc.)
10. Add TubeConfig struct for parameters
11. Remove redundant fields

### Long-Term (Type Safety)
12. Introduce FacetIndex/VertexIndex newtypes
13. Add rotation number / action newtypes
14. Enforce invariants in constructors
15. Property-based tests

---

## Dead Code List

**Fields:**
- `omega_matrix` in PolytopeData

**Functions (truly unused):**
- `deduplicate_vertices`
- `symplectic_form_2d`
- `is_symplectic`
- `get_two_face`

**Functions (test-only, should be #[cfg(test)]):**
- `quat_i()`, `quat_j()`, `quat_k()`
- `validate_basis_in_tf`
- `compute_transition_matrix_ch2021`
- `rotation_number_direct`

---

## Test Coverage Gaps

### Critical: Shear Case UNTESTED
`find_fixed_point_on_line` (algorithm.rs:357-455) handles det(A-I) ~= 0 with three sub-cases:
1. A ~= I and b ~= 0: All points are fixed
2. A ~= I and b != 0: No fixed points
3. Rank-1 case: Fixed points form a line

**Needed tests:**
```rust
#[test] fn test_shear_case_line_of_fixed_points() { ... }
#[test] fn test_shear_case_a_equals_identity() { ... }
#[test] fn test_shear_case_no_solution() { ... }
```

### Error Branches Never Tested

| Location | Error Case |
|----------|-----------|
| algorithm.rs:334 | `try_inverse()` returns None |
| algorithm.rs:613-617 | "Tube has no transitions" |
| algorithm.rs:648-650 | "r_dot_n ~= 0 during reconstruction" |
| algorithm.rs:663-667 | Orbit closure verification fails |
| preprocess.rs:208-212 | "No vertices found" |
| trivialization.rs:62 | "Degenerate 2-face: M not invertible" |

### 4-Simplex Test Should Be Strict
**Current**: Accepts both success and failure
**Expected**: Tube should reject (has Lagrangian 2-faces)
