# Rust Package Complexity Audit

This document collects sources of complexity, confusion, and potential issues in the `rust_viterbo` crate. Each entry should be actionable and help future developers understand or improve the code.

---

## How to Contribute

When reviewing a file, look for:

1. **UNCITED claims**: Mathematical assertions without paper/theorem references
2. **Magic numbers**: Hardcoded tolerances (1e-6, 1e-10) without justification
3. **Complex control flow**: Nested conditionals, early returns that are hard to follow
4. **Naming confusion**: Variables/functions with unclear or misleading names
5. **Dead code**: Unused functions, commented-out blocks, unreachable branches
6. **Missing error handling**: Unwraps, panics, silent failures
7. **Algorithm complexity**: O(n!) or exponential algorithms without warnings
8. **Coupling issues**: Functions that depend on global state or hidden assumptions
9. **Test gaps**: Important code paths without test coverage
10. **Documentation debt**: Outdated comments, missing doc comments

Format each finding as:

```markdown
### [Category] Short description

**File:** `path/to/file.rs:line_number`

**Description:** What the issue is and why it matters.

**Suggestion:** How it could be improved (optional).
```

---

## Summary

| Category | Count | Most Affected Files |
|----------|-------|---------------------|
| UNCITED claims | 25+ | tube.rs, symplectic.rs, hk2019.rs, billiard.rs |
| Magic numbers | 30+ | tube.rs, hk2019.rs, billiard_lp.rs, compute.rs |
| Test gaps | 20+ | tube.rs, polygon.rs, polytope.rs, perturbation.rs |
| Documentation debt | 15+ | result.rs, ffi/lib.rs, types.rs |
| Missing error handling | 10+ | hk2019.rs, billiard_lp.rs, ffi/lib.rs |
| Complex control flow | 8 | tube.rs, hk2019.rs, billiard_lp.rs |
| Coupling issues | 8 | polytope.rs, compute.rs, ffi/lib.rs |
| Algorithm complexity | 5 | hk2019.rs, billiard_lp.rs, geom/polytope.rs |
| Naming confusion | 5 | affine.rs, billiard.rs, polytope.rs |
| Dead code | 3 | hk2019.rs, tube.rs, result.rs |

---

## Findings by File

### algorithm/src/tube.rs

#### [UNCITED] Orthonormal basis approach for 2-face inverse trivialization

**File:** `algorithm/src/tube.rs:148-210`

**Description:** The function `inverse_trivialization_2face` uses an orthonormal basis construction for projecting onto 2-face tangent space. The comment at line 148 correctly flags this as UNCITED.

**Suggestion:** Cite a standard reference for affine subspace projection, or add derivation in the thesis/spec document.

#### [UNCITED] Time-to-crossing formula

**File:** `algorithm/src/tube.rs:309-325`

**Description:** The formula `t(p) = h_k (h_j - n_j · p) / (2 ω(n_k, n_j))` is stated with "needs CH2021 time formula citation". This IS derived in `tube-geometry-spec.md` Section 3.2.

**Suggestion:** Update comment to cite `tube-geometry-spec.md §3.2`.

#### [UNCITED] Reeb velocity formula

**File:** `algorithm/src/tube.rs:348`

**Description:** The Reeb velocity formula `v_k = (2/h_k) J n_k` needs citation. This IS stated in `tube-geometry-spec.md` Section 2.1.

**Suggestion:** Update comment to cite `tube-geometry-spec.md §2.1`.

#### [UNCITED] Flow map composition

**File:** `algorithm/src/tube.rs:388`

**Description:** Flow map computed as sum of base and time-dependent terms is uncited.

**Suggestion:** Cite `tube-geometry-spec.md §3.3-3.4`.

#### [UNCITED] Rotation accumulates additively

**File:** `algorithm/src/tube.rs:471`

**Description:** Rotation additivity assumption is justified in `tube-geometry-spec.md §4.5`.

**Suggestion:** Update comment to cite `tube-geometry-spec.md §4.5`.

#### [Magic numbers] Multiple tolerance values without central documentation

**File:** `algorithm/src/tube.rs:169, 182, 201, 256, 298, 639, 731, 737, 748`

**Description:** Tolerances include `1e-10` (degeneracy), `1e-20` (degenerate triangles), `1e-6` (warnings), `-0.01` (barycentric). These serve different purposes but are scattered without central reference.

**Suggestion:** Create named constants at module level with documented purposes.

#### [Complex control flow] Multiple fallback paths in inverse_trivialization_2face

**File:** `algorithm/src/tube.rs:149-210`

**Description:** Three fallback paths for degenerate cases with no logging or tests for fallback behavior.

**Suggestion:** Add debug logging and unit tests for degenerate inputs.

#### [Test gaps] No tests for extend_tube, get_extensions, solve_closed_tube, reconstruct_witness

**File:** `algorithm/src/tube.rs:407-763`

**Description:** Critical tube extension and closure pipeline lacks direct unit tests.

**Suggestion:** Add integration tests using simple polytope (e.g., tesseract).

#### [Documentation debt] Root tube rotation initialization differs from spec

**File:** `algorithm/src/tube.rs:68` vs `tube-geometry-spec.md:214-224`

**Description:** Code uses `rotation: 0.0` while spec suggests including starting 2-face rotation for earlier pruning.

**Suggestion:** Document which approach is used and why.

---

### algorithm/src/hk2019.rs

#### [UNCITED] Witness segment_times formula not from HK2017

**File:** `algorithm/src/hk2019.rs:452-453`

**Description:** `segment_times = beta * total_time` conversion has no citation. The relationship between β weights and Reeb flow segment times is not established.

**Suggestion:** Either cite justification or mark as placeholder values.

#### [Magic numbers] Multiple hardcoded tolerances

**File:** `algorithm/src/hk2019.rs:167,174,179,248,250,258`

**Description:** Tolerances `1e-10`, `1e-8`, `1e-12` with different magnitudes and no documented rationale.

**Suggestion:** Define named constants with doc comments.

#### [Complex control flow] Nested subset enumeration callback

**File:** `algorithm/src/hk2019.rs:152-199`

**Description:** Closure callback modifies external state with early returns, making control flow hard to follow.

**Suggestion:** Restructure to return vertex list from Phase 1, then process edges in Phase 2.

#### [Algorithm complexity] O(C(n,k)) + O(V²) per permutation, then O(n!) permutations

**File:** `algorithm/src/hk2019.rs:152-272`

**Description:** Memory usage ~290 MB for 10! permutations. Undocumented complexity.

**Suggestion:** Document complexity and consider lazy permutation generation.

#### [Documentation debt] Witness breakpoints always empty

**File:** `algorithm/src/hk2019.rs:455`

**Description:** `breakpoints: vec![]` means witness cannot be verified geometrically.

**Suggestion:** Implement breakpoint computation or document limitation.

#### [Test gaps] Tests accept failures and use weak assertions

**File:** `algorithm/src/hk2019.rs:508-527, 542-556`

**Description:** Tests marked `#[ignore]`, use 12.5% tolerance, accept QP solver failure.

**Suggestion:** Add ground-truth tests for known-correct configurations.

#### [Documentation debt] Module named "hk2019" but cites "HK2017"

**File:** `algorithm/src/hk2019.rs:1,35-48`

**Description:** Discrepancy between 2017 and 2019 unexplained.

**Suggestion:** Clarify if same paper (arxiv vs published) or correct naming.

---

### algorithm/src/billiard.rs

#### [UNCITED] Polar body vertex formula

**File:** `algorithm/src/billiard.rs:165-170`

**Description:** Duality formula `polar vertices = n_i/h_i` marked as "UNCITED standard result".

**Suggestion:** Cite Schneider (2014) or Rockafellar's "Convex Analysis".

#### [Magic numbers] EPS_LAGR_PROD = 1e-10 lacks justification

**File:** `algorithm/src/billiard.rs:36`

**Description:** Threshold for detecting "purely q-space" vs "purely p-space" facets is ad-hoc.

**Suggestion:** Document rationale for the specific value.

#### [Missing error handling] Silent failure in from_hrep

**File:** `algorithm/src/billiard.rs:111-122`

**Description:** When line_intersection returns None, vertex silently not added. Debug-only assertion.

**Suggestion:** Make Result-returning function or use `.expect()` in release builds.

#### [Test gaps] No tests for degenerate polygon inputs

**File:** `algorithm/src/billiard.rs:541-948`

**Description:** No tests for thin polygons, near-parallel edges, near-zero heights.

**Suggestion:** Add edge case tests for numerical instability.

#### [Naming confusion] p_vertex_local vs p_facet_local semantic overlap

**File:** `algorithm/src/billiard.rs:60-63`

**Description:** Relationship between vertex and facet local indices not documented.

**Suggestion:** Add doc comment explaining geometric relationship.

---

### algorithm/src/billiard_lp.rs

#### [Magic numbers] Multiple tolerances without justification

**File:** `algorithm/src/billiard_lp.rs:37,44,50,374`

**Description:** `EPS=1e-10`, `MARGIN=0.01`, `SEPARATION=0.1`, `DEGEN_TOL=1e-6` acknowledged as "ad-hoc engineering choices".

**Suggestion:** Document relationship to input scales and why magnitudes differ by 10,000x.

#### [UNCITED] LP epigraph reformulation

**File:** `algorithm/src/billiard_lp.rs:76`

**Description:** Standard technique but citation missing in code. Archive doc cites Boyd & Vandenberghe §4.2.5.

**Suggestion:** Add citation in code.

#### [Missing error handling] LP solver errors silently return None

**File:** `algorithm/src/billiard_lp.rs:231-245, 320-334`

**Description:** No distinction between "no valid trajectory" and "LP solver failure".

**Suggestion:** Return Result type or log errors.

#### [Inconsistent behavior] 2-bounce LP vs 3-bounce LP margin handling

**File:** `algorithm/src/billiard_lp.rs:293-294 vs 134-136`

**Description:** 3-bounce uses MARGIN bounds, 2-bounce uses (0,1). Unexplained inconsistency.

**Suggestion:** Unify handling or document why cases differ.

#### [Coupling issues] count_lp_solves overestimates actual solves

**File:** `algorithm/src/billiard_lp.rs:650-654`

**Description:** Returns theoretical max but algorithm skips degenerate cases, giving misleading metrics.

**Suggestion:** Count actual LP solves or rename to `theoretical_max_lp_solves`.

---

### algorithm/src/affine.rs

#### [UNCITED] Reference to non-existent thesis section

**File:** `algorithm/src/affine.rs:7`

**Description:** References "thesis §4.3" but section numbering doesn't match.

**Suggestion:** Update citation to correct section label.

#### [Test gaps] Missing tests for AffineFunc::compose, AffineMap2D::fixed_point edge cases

**File:** `algorithm/src/affine.rs:46-54, 84-90`

**Description:** Only tests special cases (diagonal matrices, identity). No tests for near-singular cases.

**Suggestion:** Add tests with general non-diagonal matrices and near-singular inputs.

#### [Naming confusion] compose appears on both structs with different semantics

**File:** `algorithm/src/affine.rs:38-44,84-90`

**Description:** `AffineMap2D::compose` composes two maps; `AffineFunc::compose` composes function with map.

**Suggestion:** Consider renaming `AffineFunc::compose` to `precompose` or `compose_with_map`.

---

### algorithm/src/polygon.rs

#### [UNCITED] Minimize only checks vertices

**File:** `algorithm/src/polygon.rs:69-88`

**Description:** Relies on LP extreme point theorem without citation.

**Suggestion:** Add citation: "Boyd & Vandenberghe, Convex Optimization, Theorem 2.6".

#### [UNCITED] Sutherland-Hodgman algorithm

**File:** `algorithm/src/polygon.rs:7`

**Description:** Mentioned but no citation to original paper.

**Suggestion:** Add citation: "Sutherland & Hodgman (1974), Communications of the ACM".

#### [Magic number] EPS_POLY = 1e-8 without analysis

**File:** `algorithm/src/polygon.rs:13-14`

**Description:** Justified as handling "chained affine transformations" but no error accumulation analysis.

**Suggestion:** Document tolerance analysis or make configurable.

#### [Test gaps] No tests for CW polygon containment, line_segment_intersection edge cases

**File:** `algorithm/src/polygon.rs:95-120, 173-189`

**Description:** Contains method handles CW orientation but only tested with CCW. No direct tests for intersection helper.

**Suggestion:** Add tests for CW polygons, parallel lines, collinear segments.

---

### algorithm/src/polytope.rs

#### [Magic numbers] EPS_FEAS, EPS_DEDUP, EPS_LAGR without theoretical justification

**File:** `algorithm/src/polytope.rs:21-26`

**Description:** Three tolerances (`1e-10`, `1e-8`, `1e-9`) with different magnitudes but no explanation for choices.

**Suggestion:** Document rationale for each tolerance value and their relationships.

#### [Coupling issues] Silent failure when two_face_rotation returns None

**File:** `algorithm/src/polytope.rs:103-106`

**Description:** Faces silently skipped without logging. After Lagrangian filter, hitting None indicates unexpected non-positive-elliptic matrix.

**Suggestion:** Add debug assertion or logging for this case.

#### [Test gaps] No negative tests for malformed input

**File:** `algorithm/src/polytope.rs:78-136`

**Description:** No tests for empty polytope, single facet, degenerate 2-faces.

**Suggestion:** Add boundary condition tests.

#### [Naming confusion] "entry" vs "exit" normals inconsistency

**File:** `algorithm/src/polytope.rs:97-101`

**Description:** Stores `entry_normal` but `i,j` are sorted order not flow order. Confusing semantics.

**Suggestion:** Store both facet indices or add method to reconstruct exit normal.

---

### algorithm/src/compute.rs

#### [Magic numbers] EPS_ROT = 0.01 without justification

**File:** `algorithm/src/compute.rs:23`

**Description:** Rotation pruning tolerance (1% of a turn) chosen without derivation.

**Suggestion:** Document relationship to expected precision of rotation calculation.

#### [Magic numbers] Perturbation seed=42 and epsilon=1e-2 hardcoded

**File:** `algorithm/src/compute.rs:115-119`

**Description:** No mathematical relationship cited for epsilon affecting rotation.

**Suggestion:** Cite or document empirical validation.

#### [Complex control flow] Redundant Lagrangian 2-face checks

**File:** `algorithm/src/compute.rs:93-102, 130-138`

**Description:** Two checks for Lagrangian faces with unclear relationship.

**Suggestion:** Clarify intent or remove redundant check.

#### [Coupling issues] AlgorithmMetadata.requires_non_lagrangian contradicts behavior

**File:** `algorithm/src/compute.rs:371, 293`

**Description:** Metadata says `requires_non_lagrangian: false` but algorithm rejects any Lagrangian 2-faces.

**Suggestion:** Set `requires_non_lagrangian: true` or clarify field semantics.

---

### algorithm/src/result.rs

#### [Magic numbers] Multiple tolerances in verify_differential_inclusion

**File:** `algorithm/src/result.rs:223, 226, 228, 241, 242, 253, 260`

**Description:** Uses `1e-14` and `1e-10` without named constants or justification.

**Suggestion:** Define named constants with documentation.

#### [Unused parameter] _tol parameter never used

**File:** `algorithm/src/result.rs:206`

**Description:** Function accepts tolerance parameter but uses hardcoded values.

**Suggestion:** Either use the passed tolerance or remove it.

#### [Documentation debt] eprintln warning box in production code

**File:** `algorithm/src/result.rs:82-97`

**Description:** Large ASCII-art warning printed via eprintln is unusual for production.

**Suggestion:** Use log/tracing crate or return warning in result.

#### [Dead code] Deprecated EmptyPolytope variant still present

**File:** `algorithm/src/result.rs:313-316`

**Description:** Marked deprecated since "0.2.0" but still in codebase.

**Suggestion:** Remove if no external consumers depend on it.

---

### geom/src/polytope.rs

#### [UNCITED] H-representation definition

**File:** `geom/src/polytope.rs:2-4`

**Description:** Standard polytope definition but marked as UNCITED.

**Suggestion:** Cite Schneider 2014, Section 1.1.

#### [Algorithm complexity] O(n⁴) vertex enumeration

**File:** `geom/src/polytope.rs:156-187`

**Description:** Brute-force enumeration undocumented. For tesseract (n=8), 4096 iterations.

**Suggestion:** Document complexity and note more efficient algorithms exist.

#### [UNCITED] Cyclic vertex ordering via atan2

**File:** `geom/src/polytope.rs:260`

**Description:** Standard computational geometry but could fail for non-convex polygons.

**Suggestion:** Cite O'Rourke's "Computational Geometry in C".

#### [Missing error handling] Silent failure in face_plane_basis

**File:** `geom/src/polytope.rs:299-301, 321, 330-331`

**Description:** Returns None for three different failure modes, propagates silently.

**Suggestion:** Return Result type or log warning.

---

### geom/src/symplectic.rs

#### [UNCITED] Multiple mathematical claims need citations

**File:** `geom/src/symplectic.rs:13-17, 62-66, 73-82, 84-105, 107-147, 149-164, 166-181`

**Description:** Quaternion structure, symplectic form, trivialization, transition matrix, Sp(2) classification, rotation number formula all need citations.

**Suggestion:** Add citations to McDuff-Salamon, de Gosson, or thesis sections.

#### [Magic number] Tolerance 1e-10 used inconsistently

**File:** `geom/src/symplectic.rs:123-127, 175`

**Description:** Implementation uses 1e-10 but tests use 1e-12.

**Suggestion:** Define named constant and standardize.

#### [Test gaps] No tests for NegativeElliptic, Shear Sp2Class variants

**File:** `geom/src/symplectic.rs:141-145`

**Description:** classify_sp2 has branches not covered by tests.

**Suggestion:** Add tests for all Sp2Class variants.

---

### geom/src/perturbation.rs

#### [Test gaps] No unit tests for perturbation module

**File:** `geom/src/perturbation.rs` (entire file)

**Description:** All testing done indirectly through other modules.

**Suggestion:** Add direct unit tests for edge cases.

#### [UNCITED] Lagrangian 2-face definition lacks citation

**File:** `geom/src/perturbation.rs:1-5`

**Description:** Should cite CH2021 Definition 3.3.

**Suggestion:** Add citation.

#### [Documentation debt] Heights not perturbed - is this correct?

**File:** `geom/src/perturbation.rs:121`

**Description:** Normals perturbed but heights unchanged. Geometric implications undocumented.

**Suggestion:** Document whether this is intentional and effects.

#### [Missing error handling] No validation of epsilon parameter

**File:** `geom/src/perturbation.rs:88-128`

**Description:** Accepts negative, very large, NaN, infinity values without validation.

**Suggestion:** Add validation or document expected range.

---

### geom/src/types.rs

#### [Documentation debt] SymplecticVector alias lacks semantic documentation

**File:** `geom/src/types.rs:12-13`

**Description:** Both `SymplecticVector` and `Vector4f` are identical types with no guidance on when to use each.

**Suggestion:** Add doc comment explaining intent of each alias.

#### [UNCITED] Coordinate convention (q₁, q₂, p₁, p₂) lacks citation

**File:** `geom/src/types.rs:3`

**Description:** Non-trivial choice affecting all matrix representations.

**Suggestion:** Add rationale or citation.

---

### ffi/src/lib.rs

#### [Magic number] Default tolerance 1e-9 mismatches internal 1e-6

**File:** `ffi/src/lib.rs:106, 118, 153, 165, 206, 218`

**Description:** FFI accepts stricter tolerance than internal validation uses.

**Suggestion:** Align defaults or document mismatch.

#### [Missing error handling] Incomplete AlgorithmError coverage

**File:** `ffi/src/lib.rs:133-143, 186-196, 239-249`

**Description:** Only handles three variants; `InvalidInput` and `SearchExhausted` would panic.

**Suggestion:** Add exhaustive match arms or catch-all.

#### [Test gaps] No Rust-level unit tests for FFI module

**File:** `ffi/src/lib.rs` (entire file)

**Description:** All testing from Python side. Type conversion and error mapping untested in Rust.

**Suggestion:** Add Rust unit tests.

#### [Code duplication] Three capacity functions share near-identical structure

**File:** `ffi/src/lib.rs:120-143, 166-196, 219-249`

**Description:** Identical patterns repeated with risk of drifting out of sync.

**Suggestion:** Extract shared helper function.

---

### optim/src/lib.rs

#### [UNCITED] Problem statement in doc comments

**File:** `optim/src/lib.rs:8-16`

**Description:** Q function from HK2017/HK2019 stated without citation.

**Suggestion:** Add citations to HK papers and/or thesis section.

#### [Missing error handling] symmetric_eigen called without symmetry validation

**File:** `optim/src/lib.rs:88, 94, 100`

**Description:** Non-symmetric matrices would produce silently incorrect results.

**Suggestion:** Add symmetry check or document assumption.

#### [Test gaps] No edge case tests for matrix analysis functions

**File:** `optim/src/lib.rs:106-144`

**Description:** No tests for singular matrices, near-zero eigenvalues, non-square matrices.

**Suggestion:** Add tests for boundary conditions.

---

## Priority Recommendations

### High Priority (correctness/reliability)

1. **Add citations for UNCITED claims** in tube.rs, symplectic.rs - these are thesis-critical
2. **Fix incomplete error handling** in ffi/lib.rs (missing AlgorithmError variants)
3. **Add tests for tube extension pipeline** - critical algorithm path untested
4. **Document tolerance hierarchy** - explain relationships between EPS_* constants

### Medium Priority (maintainability)

1. **Consolidate magic numbers** into named constants with documentation
2. **Add tests for edge cases** in polygon.rs, polytope.rs, perturbation.rs
3. **Resolve spec/code inconsistencies** (tube rotation initialization, metadata fields)
4. **Extract duplicate code** in ffi/lib.rs

### Low Priority (cleanup)

1. **Remove dead code** (deprecated EmptyPolytope, unused _c variable in hk2019.rs)
2. **Fix documentation typos** (symplectic.rs "facat" → "facet")
3. **Standardize tolerance values** across tests (1e-10 vs 1e-12)

