# Tube Crate Evaluation

Comprehensive evaluation of `packages/rust_viterbo/tube/` with improvement suggestions.

**Date**: 2026-02-01
**Scope**: Architecture, code quality, test coverage, type safety, spec alignment

---

## Executive Summary

The tube crate is well-structured with good mathematical documentation, but has accumulated complexity in `algorithm.rs` (1100 lines). Key improvement areas:

1. **Critical bugs/issues**: `p_start` not being refined (flagged as suspicious), shear case untested
2. **Dead code**: 13 items including `omega_matrix`, `deduplicate_vertices`, `symplectic_form_2d`
3. **Naming**: `apply_quat_i` serves dual role (quaternion i vs symplectic J) - needs separate functions
4. **Complexity**: `algorithm.rs` should be split into 4-5 submodules
5. **Type safety**: Missing newtypes for indices, rotation numbers, action values
6. **Test gaps**: Shear case (98 lines of complex math) has zero test coverage

---

## 1. Flagged Issues (Require Jörn's Input)

### 1.1 p_start Not Refined (algorithm.rs:233-236)
```rust
// For now, we keep p_start unchanged (conservative: may include invalid starts)
```
**Status**: Flagged as suspicious. Unclear why this is "conservative" or if it affects correctness.

### 1.2 Rotation Accumulation Proof Missing
The code does `tube.rotation + exit_2face.rotation` (algorithm.rs:244). Mathematical justification needs to be written up:
- Infinitesimal case → integral for smooth → limit for polytopes (discrete sum)

### 1.3 apply_quat_i Dual Role
`apply_quat_i` is used for both:
- Quaternionic multiplication by i (quaternion.rs)
- Symplectic J matrix application (symplectic_form, reeb_vector)

**Action needed**: Create two functions with different names:
```rust
pub fn symplectic_j(v: &Vector4<f64>) -> Vector4<f64>  // Symplectic geometry
pub fn quaternion_i(v: &Vector4<f64>) -> Vector4<f64>  // Quaternion multiplication
// Both equal, but serve different conceptual roles
```

Also: The `apply_quat_*` pattern is premature optimization. Should be `quat_i() * v` for readability.

---

## 2. Dead Code

| Item | Location | Notes |
|------|----------|-------|
| `omega_matrix` field | preprocess.rs:39 | Computed but never accessed |
| `deduplicate_vertices` | geometry.rs:143 | Never called |
| `symplectic_form_2d` | quaternion.rs:100 | Never called |
| `is_symplectic` method | types.rs:125 | Never called |
| `get_two_face` method | preprocess.rs:69 | Only `get_two_face_enriched` used |
| `quat_i/j/k()` functions | quaternion.rs:23,40,57 | Only in tests (verify optimized versions) |
| `validate_basis_in_tf` | trivialization.rs:167 | Only in tests, has `#[allow(dead_code)]` |
| `compute_transition_matrix_ch2021` | trivialization.rs:123 | Only in tests |
| `rotation_number_direct` | trivialization.rs:160 | Only in tests |

**Recommendation**: Remove truly dead code, mark test-only functions with `#[cfg(test)]`.

---

## 3. Naming Issues

### 3.1 Two-Face Naming Inconsistency
Mixed conventions throughout:
- Types: `TwoFace`, `TwoFaceEnriched`
- Fields: `two_faces`, `two_faces_enriched`
- Tests: `test_24_cell_no_lagrangian_2faces` (with digit)
- Comments: "2-face" (hyphenated)

**Recommendation**: Standardize on `two_face` in code, "2-face" in comments/docs.

### 3.2 FlowDirection Enum Variants
```rust
ItoJ, JtoI  // Current (wrong)
IToJ, JToI  // Should be (PascalCase)
```

### 3.3 Getter Naming
```rust
get_two_face()          // Current
two_face()              // Rust convention (no get_ prefix)
```

### 3.4 Confusing Basis Access (algorithm.rs:272)
```rust
let b_entry = &entry_2face.basis_exit;  // Confusing!
```
Taking `basis_exit` from `entry_2face` is mathematically correct but naming is confusing.

---

## 4. Complexity Hotspots

### 4.1 algorithm.rs is Too Large (1100 lines)
**Recommendation**: Split into submodules:
- `algorithm/mod.rs` - Main search loop, tube_capacity()
- `algorithm/tube_ops.rs` - create_root_tube, extend_tube, get_extensions
- `algorithm/flow.rs` - compute_facet_flow
- `algorithm/fixed_points.rs` - find_closed_orbit, find_fixed_point_on_line
- `algorithm/reconstruction.rs` - reconstruct_orbit, untrivialize_point

### 4.2 Complex Functions (>90 lines)

| Function | Lines | Issues |
|----------|-------|--------|
| `find_fixed_point_on_line` | 98 | 4-5 nesting levels, 15 local vars, 3 case branches |
| `intersect_line_with_polygon_min_action` | 98 | Complex geometry, many edge cases |
| `reconstruct_orbit` | 93 | Mixes validation, computation, state building |
| `compute_facet_flow` | 67 | Three phases mixed together |
| `enumerate_vertices_4d` | 57 | 4 nested loops, 6 nesting levels |

**Recommendation**: Decompose each into focused helper functions (~20 lines each).

---

## 5. Type Safety Opportunities

### 5.1 High Priority Newtypes

```rust
// Prevent index confusion
pub struct FacetIndex(usize);
pub struct VertexIndex(usize);

// Encode mathematical constraints
pub struct TwoFaceRotation(f64);     // Guaranteed in (0, 0.5)
pub struct AccumulatedRotation(f64); // Tube rotation sum
pub struct PositiveAction(f64);      // Always > EPS

// Distinguish coordinate systems
pub struct TrivializedPoint2D(Vector2<f64>);
pub struct UnitVector4(Vector4<f64>);
```

### 5.2 Invariants Not Enforced

| Type | Invariant | Current | Recommendation |
|------|-----------|---------|----------------|
| `Polygon2D` | CCW order, ≥3 vertices | Comment only | Validate in constructor |
| `TwoFace` | i < j | Comment only | Enforce in constructor |
| `Tube.facet_sequence` | ≥2 elements | None | Validate, or use NonEmpty |
| Flow maps | det(A) = 1 | `is_symplectic()` exists | Add debug_assert! |

### 5.3 Silent Corrections (Anti-pattern)
```rust
// trivialization.rs:153 - silently clamps instead of erroring
let half_trace = 0.5 * trace.clamp(-2.0, 2.0);
```
**Recommendation**: Return `Result` for out-of-range values.

---

## 6. Test Coverage Gaps

### 6.1 Critical: Shear Case UNTESTED
`find_fixed_point_on_line` (algorithm.rs:357-455) handles det(A-I) ≈ 0 with three sub-cases:
1. A ≈ I and b ≈ 0: All points are fixed
2. A ≈ I and b ≠ 0: No fixed points
3. Rank-1 case: Fixed points form a line

**Current coverage**: Only diagnostic prints, no actual tests.

**Needed tests**:
```rust
#[test] fn test_shear_case_line_of_fixed_points() { ... }
#[test] fn test_shear_case_a_equals_identity() { ... }
#[test] fn test_shear_case_no_solution() { ... }
```

### 6.2 Error Branches Never Tested

| Location | Error Case |
|----------|-----------|
| algorithm.rs:334 | `try_inverse()` returns None |
| algorithm.rs:613-617 | "Tube has no transitions" |
| algorithm.rs:648-650 | "r_dot_n ≈ 0 during reconstruction" |
| algorithm.rs:663-667 | Orbit closure verification fails |
| preprocess.rs:208-212 | "No vertices found" |
| trivialization.rs:62 | "Degenerate 2-face: M not invertible" |

### 6.3 4-Simplex Test Should Be Strict
**Current**: Accepts both success and failure
**Expected**: Tube should reject (has Lagrangian 2-faces)

```rust
#[test]
fn test_four_simplex_rejected_lagrangian() {
    let result = tube_capacity(&fixtures::four_simplex());
    assert!(matches!(result, Err(TubeError::HasLagrangianTwoFaces)));
}
```

### 6.4 Missing Test Categories
- Property-based tests (flow map symplecticity, polygon convexity)
- Benchmarks for performance regression
- Documented regression tests

---

## 7. API & Rust Guidelines

### 7.1 Panic Risks
```rust
// geometry.rs:29 - can panic on NaN
angle_a.partial_cmp(&angle_b).unwrap()
// Fix: .unwrap_or(std::cmp::Ordering::Equal)

// algorithm.rs:159 - panic instead of Result
None => panic!("Cannot create root tube for Lagrangian 2-face")
// Fix: Return Result or use debug_assert!
```

### 7.2 Unwraps Without Context
```rust
tube.facet_sequence.last().unwrap()  // Safe but unclear why
// Fix: .expect("facet_sequence is never empty")
```

### 7.3 Public Fields With Invariants
`Polygon2D.vertices` and `TwoFace.i/j` are public but have documented invariants that can be violated by direct access.

**Options**:
- Make fields private with accessors
- Add `#[non_exhaustive]` to prevent external construction
- Document construction pattern clearly

---

## 8. Spec Alignment Issues

### 8.1 Two-Face Representation Split
- **Math**: A 2-face F_ij is a unified concept
- **Code**: Split into `TwoFace` + `TwoFaceEnriched`
- **Impact**: API confusion, duplicate lookups

### 8.2 FlowDirection Stored Redundantly
- **Math**: Direction derived from sign(ω(n_i, n_j))
- **Code**: Stored explicitly as enum
- **Impact**: Redundancy, potential inconsistency

### 8.3 Normals Stored Redundantly
`TwoFaceEnriched` stores `entry_normal`/`exit_normal` as full Vector4, but these can be looked up via indices from PolytopeData.

### 8.4 Fixed Point Cases Not Algebraically Typed
Three branches in `find_fixed_point_on_line` (regular, shear, identity) could be:
```rust
enum FixedPointCase {
    Regular { solution: Vector2<f64> },
    Shear { line: ParametricLine, polygon: &Polygon2D },
    Identity { polygon: &Polygon2D },
}
```

---

## 9. Prioritized Recommendations

### Immediate (Bug Fixes)
1. Investigate `p_start` not being refined
2. Fix 4-simplex test to be strict
3. Add tests for shear case

### Short-Term (Code Quality)
4. Create separate `symplectic_j()` function (parallel to `quaternion_i()`)
5. Remove dead code
6. Fix `FlowDirection` enum variant naming
7. Add `.expect()` context to safe unwraps

### Medium-Term (Refactoring)
8. Split `algorithm.rs` into submodules
9. Decompose complex functions (find_fixed_point_on_line, etc.)
10. Add TubeConfig struct for parameters
11. Remove redundant fields (FlowDirection, duplicate normals)

### Long-Term (Type Safety)
12. Introduce FacetIndex/VertexIndex newtypes
13. Add rotation number / action newtypes
14. Enforce invariants in constructors
15. Property-based tests

---

## Appendix: Full Dead Code List

<details>
<summary>13 items identified</summary>

**Fields**:
- `omega_matrix` in PolytopeData

**Functions (truly unused)**:
- `deduplicate_vertices`
- `symplectic_form_2d`
- `is_symplectic`
- `get_two_face`

**Functions (test-only, should be #[cfg(test)])**:
- `quat_i()`, `quat_j()`, `quat_k()`
- `validate_basis_in_tf`
- `compute_transition_matrix_ch2021`
- `rotation_number_direct`

</details>
