# Critical Review: developer-spec-v2.md

**Reviewer:** Claude Code agent
**Date:** 2026-01-25
**Scope:** Gaps, ambiguities, open questions, contradictions, style issues

---

## Handoff Notes (for next agent)

**Your task:** Fix the spec (developer-spec-v2.md) according to §10 recommendations. Update this review as you go.

**Key context:**
1. **Truth hierarchy:** Math papers → Thesis → Spec math → Spec Rust. Never use Rust code to justify conventions; go to the math source.
2. **Trivialization normal convention (decided):** Use the **exited facet's normal** (the facet we're leaving). Document this in TwoFaceEnriched.
3. **Facet sequence semantics (decided):** `[i, j]` means "at 2-face F_{i,j}, entered facet j from facet i, about to flow along j."
4. **Near-singular handling:** Runtime error, don't silently assume genericity (§0.6).
5. **Testing without ground truth:** Use axioms, orbit validity, internal invariants (§9.2-9.4). Don't rely solely on known capacity values.

**Files to read:**
- This review: `packages/rust_viterbo/docs/review-spec-v2.md`
- The spec: `packages/rust_viterbo/docs/developer-spec-v2.md`
- For citations: `docs/papers/` (contains CH2021 sections), `packages/latex_viterbo/chapters/` (thesis)

**Workflow:** For each §10 recommendation, fix the spec, then mark the recommendation as done in this review.

---

## Executive Summary

The developer-spec-v2.md is a substantial improvement in structure and mathematical rigor compared to v1. However, several categories of issues remain:

1. **Major gaps:** Missing treatment of Lagrangian 2-face handling in Tube algorithm, incomplete action lower bound computation
2. **Ambiguities:** Coordinate system conventions not fully consistent, trivialization depends on "entry normal" but definition varies
3. **Open questions:** What happens when polytopes have both Lagrangian and non-Lagrangian 2-faces?
4. **Contradictions:** Document vs. mathematical-claims.md have inconsistent citations for HK2017 vs HK2019
5. **Style issues:** Progressive disclosure makes some forward references confusing

---

## 0. Clarifications from Project Owner (2026-01-25)

These clarifications resolve several ambiguities identified below:

### 0.1 Trivialization Basis (re: Section 3.1) — RESOLVED

The quaternion-based trivialization τ(V) = (⟨V, J'n⟩, ⟨V, J''n⟩) is **valid for non-Lagrangian 2-faces**.

Key insight: The coordinate vectors J'n, J''n need not be tangent to the 2-face. We only need the 2-face to project non-degenerately onto these coordinates:
- **Non-Lagrangian 2-faces:** Project to a 2D region → valid coordinate system
- **Lagrangian 2-faces:** Jn lies in the 2-face tangent space (since ω(n₁, n₂) = ⟨Jn₁, n₂⟩ = 0 means Jn₁ ⊥ n₂, and Jn₁ ⊥ n₁ already), so the 2-face projects to a 1D line → degenerate

This degeneracy is precisely why the tube algorithm doesn't handle Lagrangian 2-faces.

### 0.2 Rotation Convention (re: Section 4.3)

Convention: **rot(init) = 0**. The tube trajectory starts ε-time after entering the second facet (and ends at 2ε-time, being straight lines inside the facet). Trajectories extend such that γ(0) lies on the 2-face. The tube is not just the interior lines—it includes the extended trajectories.

Rotation is **non-decreasing** as one extends a finite trajectory in either direction (both smooth and polytope cases). The algorithm uses ≥0 rotation increments.

### 0.3 Coordinate Systems for p_start, p_end (re: Section 3.4)

Both `p_start` and `p_end` should exist (for debugging; can remove dead code later). They use their respective 2-face coordinate systems.

**Convention decided:** Use the **exited facet's normal** (the facet we're leaving) for trivialization. For a tube with `facet_sequence: [i, j, k, ...]`:
- Start 2-face F_{i,j} is trivialized using n_i (exited facet)
- After flowing along j to 2-face F_{j,k}, that 2-face is trivialized using n_j (exited facet)

This must be documented clearly in `TwoFaceEnriched.polygon_2d` and in the `compute_facet_flow` function.

### 0.4 Mixed Lagrangian Polytopes (re: Section 4.1)

Confirmed: **No algorithm is currently designed** to handle polytopes with both Lagrangian and non-Lagrangian 2-faces. This is a known limitation.

### 0.5 Lagrangian 2-Faces in Tube Algorithm (re: Section 4.2)

Confirmed: The tube algorithm is **not designed** for Lagrangian 2-faces.

### 0.6 Degenerate Fixed Points (re: Section 4.4)

In the generic case, there is 0 or 1 fixed point per tube. This can be seen by perturbation: every factor of ψ can be perturbed (by perturbing the polytope) such that the product no longer has eigenvalue 1.

**Recommendation:** Do not silently assume genericity. Instead, **runtime error** if numerics turn nearly singular.

### 0.7 Naming and Complexity (re: Sections 5.1, 5.4)

- HK2017 naming: agreed, use consistently
- Complexity claims: not a priority. Delete or mark as unverified.

### 0.8 Tolerance Hierarchy (re: Section 3.5)

Not a priority. More important to detect when numerics are wrong and react, than to theorize tolerance choices in advance.

---

## 1. Documented Gaps (Explicitly Incomplete)

### 1.1 HK2017 QP Solver Incompleteness (Section 3.3)

**Location:** Lines 1689-1694

> "CRITICAL WARNING: Q is indefinite (neither convex nor concave). The maximum may occur at: Vertices (0D faces), Edges (1D faces), Higher-dimensional faces. A complete implementation requires a global QCQP solver. Checking only vertices is **incomplete**."

**Issue:** This is documented but no guidance is given on:
- Which QCQP solvers are suitable
- How to handle the indefinite case algorithmically
- Whether branch-and-bound on face enumeration is sufficient

### 1.2 Degenerate Fixed Point Case (Section 2.11)

**Location:** Lines 1393-1396

```rust
if det.abs() < EPS {
    // Degenerate: line or plane of fixed points
    // Handle separately...
    return find_fixed_point_set(tube);
}
```

**Issue:** `find_fixed_point_set` is referenced but never defined. The degenerate case (entire line/plane of fixed points) is mathematically important and occurs in practice.

### 1.3 Pentagon Bug Not Addressed

**Location:** Referenced in mathematical-claims.md but not in developer-spec-v2.md

**Issue:** The known bug where pentagon returns 2.127 instead of 3.441 is documented in mathematical-claims.md (line 132) and the original developer-spec.md (line 155), but developer-spec-v2.md does not mention this known failure case or what might cause it.

---

## 2. Undocumented Gaps

### 2.1 Missing: Vertex Enumeration Algorithm

**Location:** Section 1.1, line 161

```rust
fn vertex_enumeration(hrep: &PolytopeHRep) -> PolytopeVRep;  // e.g., double description method
```

**Issue:** This is declared but never specified. Vertex enumeration is non-trivial and the "double description method" is just a hint. Should reference:
- Avis & Fukuda's `lrslib`
- `qhull` library
- Or specify the algorithm in detail

### 2.2 Missing: Polygon CCW Sorting

**Location:** Section 1.14, line 717

```rust
let polygon_2d = sort_ccw(polygon_2d);
```

**Issue:** `sort_ccw` is called but not defined. For convex polygons this is typically atan2-based sorting from centroid, but the exact algorithm should be specified since edge cases (collinear points, coincident vertices) matter.

### 2.3 Missing: Convex Polygon Intersection

**Location:** Section 2.10, line 1354

```rust
let new_p_end = intersect_polygons(
    &apply_affine_map(&phi, &tube.p_end),
    &two_face.polygon_2d,
);
```

**Issue:** `intersect_polygons` is referenced without definition. Sutherland-Hodgman is mentioned in a comment but:
- Sutherland-Hodgman is for clipping, not intersection of two convex polygons
- For two convex polygons, O'Rourke's algorithm or similar is standard
- Edge cases (empty result, point/line result) need handling

### 2.4 Missing: Point-in-Polygon Test

**Location:** Section 2.11, line 1403

```rust
if !point_in_polygon(&s, &tube.p_start) {
```

**Issue:** Algorithm not specified. Winding number vs crossing number is mentioned in a comment but the actual implementation is undefined.

### 2.5 Missing: Action Lower Bound Computation

**Location:** Section 3.4, line 1725

```rust
if tube.action_lower_bound() >= best_action {
    continue;  // Prune
}
```

**Issue:** `action_lower_bound()` is never defined. This is crucial for branch-and-bound efficiency. Options include:
- Minimum over `action_func` on `p_start` polygon
- Linear programming to find minimum of affine function on convex polytope
- Closed-form for 2D case

### 2.6 Missing: Cone Membership Solver

**Location:** Section 2.3, lines 934-937

```rust
fn is_valid_reeb_velocity(
    velocity: &Vector4<f64>,
    active_facets: &[usize],
    reeb_vectors: &[Vector4<f64>],
) -> bool {
    // Solve: velocity = Σ λ_i R_i with λ_i ≥ 0
    // This is a linear feasibility problem
    solve_cone_membership(velocity, active_facets, reeb_vectors)
}
```

**Issue:** `solve_cone_membership` is never defined. This requires either:
- LP solver
- Specialized cone membership algorithm (Farkas lemma based)

### 2.7 Missing: Billiard LP Formulation Details

**Location:** Section 3.2, lines 1639-1650

The LP variables and constraints are sketched but the actual LP formulation is incomplete:
- The "Reeb velocity: displacement = time × Reeb vector" constraint is not mathematically specified
- The closure constraint is not formalized
- No mention of which LP solver to use

### 2.8 Missing: Affine Map Composition

**Location:** Section 2.10, lines 1367-1368

```rust
flow_map: compose_affine(&phi, &tube.flow_map),
action_func: add_affine_funcs(&tube.action_func, &compose_with_map(&time_func, &tube.flow_map)),
```

**Issue:** `compose_affine`, `add_affine_funcs`, and `compose_with_map` are used but not defined. These are straightforward but should be explicit:
- `compose_affine(f, g)(x) = f(g(x))` where `f(x) = Ax + b`, `g(x) = Cx + d` gives `(AC)x + (Ad + b)`
- Order of composition matters

---

## 3. Ambiguities

### 3.1 Trivialization: Which Normal? (RESOLVED — see 0.1)

**Location:** Section 1.14 vs Section 2.10

In Section 1.14 (line 703-704):
```rust
fn trivialize_two_face(
    two_face: &TwoFace,
    vertices: &[Vector4<f64>],
    entry_normal: &Vector4<f64>,  // <-- passed as parameter
```

In Section 2.10 (line 1261):
```rust
// 4. Convert to exit coords: q_2d = trivialize(n_curr, q_4d - centroid_exit)
```

**Remaining issue:** The trivialization is relative to a normal, but:
- Section 1.14 takes `entry_normal` as a parameter (unclear which facet this refers to)
- Section 2.10 uses `n_curr` (the current facet's normal)
- `TwoFaceEnriched` does not clearly store which normal was used for its `polygon_2d`

The trivialization formula itself is valid (see 0.1), but the **convention** (entry vs exit normal) needs to be documented consistently.

### 3.2 Closed vs Open Facet Sequences

**Location:** Section 2.8, lines 1137-1153

```rust
fn is_closeable(&self, two_faces: &[TwoFace]) -> bool {
    // ...
    if self.facets[self.facets.len() - 1] != self.facets[0] {
        return false;
    }
```

**Issue:** Are facet sequences stored with repeated first/last element (closed) or without (implicitly closed)? The code checks `facets[n-1] == facets[0]` suggesting repeated storage, but `Tube::facet_sequence` in Section 2.9 uses `[i_0, i_1, ..., i_k, i_{k+1}]` without clear closure semantics.

### 3.3 Root Tube Initialization

**Location:** Section 2.9, lines 1203-1213

```rust
fn create_root_tube(two_face: &TwoFaceEnriched) -> Tube {
    Tube {
        facet_sequence: vec![two_face.i, two_face.j],
        p_start: two_face.polygon_2d.clone(),
        p_end: two_face.polygon_2d.clone(),
        // ...
    }
}
```

**Issue:** A "root tube" has facet_sequence `[i, j]` but:
- Does this mean we're starting on 2-face F_{i,j}?
- What facet do we flow along? Neither i nor j is clearly designated as the "current" facet
- The tube extension logic expects `seq[len-2]` to be the "previous" facet and `seq[len-1]` to be "current", but for length-2 sequence this is unclear

### 3.4 Tube p_start vs p_end Semantics

**Location:** Section 2.9

```rust
p_start: Polygon2D,           // set of valid starting points
p_end: Polygon2D,             // set of valid ending points
```

**Issue:** Are these in the same coordinate system? The flow map transforms from start 2-face coordinates to end 2-face coordinates, but it's unclear if:
- `p_start` is in start 2-face coordinates
- `p_end` is in end 2-face coordinates (different basis!)
- Or both are in some common reference frame

### 3.5 Tolerance Hierarchy

**Location:** Section 1.16, lines 797-803

```rust
const EPS: f64 = 1e-10;
const EPS_LAGRANGIAN: f64 = 1e-9;
const EPS_UNIT: f64 = 1e-9;
const EPS_FEASIBILITY: f64 = 1e-10;
const EPS_DEDUP: f64 = 1e-8;
const EPS_ROTATION: f64 = 0.01;
```

**Issue:** The relationship between these tolerances is unclear:
- Why is `EPS_LAGRANGIAN` larger than `EPS`?
- `EPS_ROTATION` is much larger (0.01 = 1% of a turn) — is this intentional?
- No guidance on when to use relative vs absolute tolerance

---

## 4. Open Questions

### 4.1 Mixed Lagrangian/Non-Lagrangian Polytopes

**Location:** Section 1.6, lines 378-381

> "A Lagrangian product K_1 × K_2 has ALL 2-faces Lagrangian. If some but not all 2-faces are Lagrangian, special handling may be needed."

**Question:** What is this "special handling"? The Tube algorithm requires no Lagrangian 2-faces (Section 3.4), and the Billiard algorithm requires all Lagrangian 2-faces. What algorithm handles the mixed case?

### 4.2 Orbit Flowing Along Lagrangian 2-Face

**Location:** Referenced in original developer-spec.md (line 79)

> "Some polytopes with lagrangian 2-faces have only minimum action orbits such that the orbit flows along a lagrangian 2-face with a breakpoint in the interior of the lagrangian 2-face."

**Question:** This case is mentioned in v1 but not in v2. Is it intentionally excluded? Does HK2017 handle it?

### 4.3 Rotation Number Sign/Direction

**Location:** Section 1.12

The rotation number is always in (0, 0.5), but is there a sign convention? Does it depend on flow direction? The document says "how much the Reeb flow rotates when crossing" but doesn't clarify if there's a signed vs unsigned convention.

### 4.4 Multiple Closed Orbits Per Tube (RESOLVED)

**Location:** Section 2.11

The `find_closed_orbits` function suggests a tube could have multiple closed orbits (returns `Vec<...>`). But the text often assumes a unique closed orbit. When can there be multiple? Only in the degenerate case?

**Resolution (per 0.6):** In the generic case, there is **0 or 1** fixed point per tube. Each factor of ψ can be perturbed (by perturbing the polytope) such that the product no longer has eigenvalue 1. Do not silently assume genericity—**runtime error** if numerics turn nearly singular.

### 4.5 Entry vs Exit Trivialization in TwoFaceEnriched

**Location:** Section 1.14, lines 751-752

```rust
polygon_2d: Vec<Vector2<f64>>,     // vertices in τ_{n_i} coordinates, CCW
```

But Section 2.12, line 1436:
```rust
let n_entry = two_face.entry_normal;
```

**Question:** Does `TwoFaceEnriched` have an `entry_normal` field? It's not listed in the struct definition (lines 732-755) but is used in `untrivialize_point`.

---

## 5. Contradictions

### 5.1 HK2017 vs HK2019 Naming

**Location:** developer-spec-v2.md Section 3.3 vs mathematical-claims.md

- developer-spec-v2.md consistently uses "HK2017" (lines 1654, 1657, 1665, 1695)
- mathematical-claims.md uses "HK2019" (line 225: "### 3.2 HK2019 Algorithm (Haim-Kislev 2017)")
- Original developer-spec.md uses "HK2019" (line 13)
- The paper citation is arXiv:1712.03494 from 2017, but it may have been published later

**Recommendation:** Settle on consistent naming. The arXiv preprint is from 2017, so "HK2017" seems appropriate.

### 5.2 Tesseract Capacity Source

**Location:** developer-spec-v2.md line 1766 vs mathematical-claims.md line 84

- developer-spec-v2.md: "HK2017 Ex 4.6"
- mathematical-claims.md: "HK2019, Example 4.6; Rudolf 2022, Example 3.5"

Should verify the actual example number in the paper.

### 5.3 Y. Nir 2013 Citation

**Location:** developer-spec-v2.md line 2151 vs mathematical-claims.md line 147

- developer-spec-v2.md: "Y. Nir 2013: On Closed Characteristics and Billiards in Convex Bodies (thesis)"
- mathematical-claims.md: "[UNCITED - NEEDS VERIFICATION]"

The thesis citation should be verified or the table entry updated.

### 5.4 Complexity Claims

**Location:** Section 3.1, lines 1604-1606

| Algorithm | Complexity |
|-----------|------------|
| Billiard | O(n₁³ × n₂³) |
| Tube | O(F! × poly) |

But original developer-spec.md (line 119) says Billiard is O(n₁³ × n₂).

**Question:** Which complexity is correct? The v2 version (n₁³ × n₂³) seems wrong since we're enumerating 3-bounce combinations in each factor.

### 5.5 Triangle Capacity Claim

**Location:** developer-spec-v2.md line 1768 vs mathematical-claims.md lines 96-103

- developer-spec-v2.md: "Triangle × Triangle (r=1): 1.5"
- mathematical-claims.md: "[UNCITED - NEEDS LITERATURE VERIFICATION]. Verified computationally"

This is a ground truth value that needs proper citation or clear marking as computational.

---

## 6. Style Issues

### 6.1 Progressive Disclosure Creates Circular References

The document uses "See section X for Y" liberally, but some references go forward to sections not yet read:
- Section 1.5 (line 328): "For the Tube algorithm, 2-faces are enriched with additional data... defined in sections 1.10-1.14"
- Section 1.11 (line 581): "// See section 1.14 for the full TwoFaceEnriched struct definition"

**Recommendation:** Either linearize the dependencies or provide a "preview" of the final struct early.

### 6.2 Inconsistent Rust Code Style

- Some functions use `&self` pattern, others use bare functions
- Some use `Result<T, E>`, others use `Option<T>`
- Some use `assert!`, others use explicit `if` checks with returns
- Mix of `Vec<[f64; 4]>` and `Vec<Vector4<f64>>`

**Recommendation:** Establish a consistent style guide.

### 6.3 Incomplete Test Fixtures

**Location:** Section 4.8, lines 2107-2113

```rust
LagrangianProductPolytope {
    K1: /* triangle */,
    K2: /* same triangle */,
}
```

**Issue:** Placeholder comments instead of actual code. Should be complete.

### 6.4 Missing Index Validation

Many code snippets index into arrays without bounds checking:
- Line 1241: `seq[seq.len() - 2]` could panic if seq.len() < 2
- Line 1464: `partial_tube = Tube { facet_sequence: seq[0..=k].to_vec(), ...}` range slicing

**Recommendation:** Either add explicit bounds assertions or document the preconditions.

### 6.5 Magic Numbers

- Line 1737: `tube.rotation <= 2.0 + EPS_ROTATION` — why 2.0? (CH2021 Prop 1.10 says (1,2) range)
- Line 1602: "at most 3 bounces" — this comes from Rudolf 2022 Thm 4 but isn't linked here

**Recommendation:** Link to the source of each magic number.

### 6.6 Struct Definitions Scattered

`TwoFaceEnriched` is first hinted in Section 1.5, partially shown in Section 1.11, and fully defined in Section 1.14. This makes it hard to understand what fields exist.

**Recommendation:** Define structs in one place with cross-references.

---

## 7. Truth Flow Violations

The spec should follow: **Math papers → Thesis → Spec math → Spec Rust**. Violations occur when:
- Mathematical claims lack citations to papers/thesis
- Rust code defines behavior instead of implementing cited math
- Inline derivations replace proper theorem references

### 7.1 Missing Citations for Key Definitions

| Section | Claim | Missing Citation |
|---------|-------|------------------|
| 1.9 Quaternion Structure | J, K matrices used for trivialization | No citation for why these specific matrices; should reference thesis or CH2021 |
| 1.10 Trivialization | τ_n(V) = (⟨V, Jn⟩, ⟨V, Kn⟩) | **Critical:** No citation for this definition. Should cite CH2021 or thesis |
| 1.10 Trivialization | "Symplectic form preservation" (line 546) | No citation for this theorem |
| 1.11 Transition Matrices | ψ_F = τ_{n_j} ∘ τ_{n_i}^{-1} | No citation; should reference CH2021 Definition X |
| 1.11 Transition Matrices | "Hyperbolic cannot occur" (line 606) | No citation for why polytope 2-faces are never hyperbolic |
| 1.12 Rotation Number | ρ(F) = (1/2π) arccos(tr(ψ)/2) | No citation; should cite CH2021 |
| 2.5 Action of Trajectories | "Action equals period" (line 1003) | No citation; fundamental claim needs reference to Hofer-Zehnder or thesis |
| 2.9 Tubes | Tube data structure and semantics | Should cite CH2021 for the tube concept |

### 7.2 Inline Derivations Without Theorem References

| Location | Issue |
|----------|-------|
| Section 2.10 (line 1200) | "Why action is affine in starting position" — gives inline proof instead of citing theorem |
| Section 2.10 (lines 1226-1231) | Time computation derivation — should reference that this follows from Reeb flow definition |
| Section 1.10 (lines 535-540) | Round-trip property — stated as assertion but not cited as theorem |

### 7.3 Rust Defining Math (Inverted Flow)

| Location | Issue |
|----------|-------|
| Section 3.1 Ambiguity (line 211-233) | Review originally treated Rust `entry_normal` parameter as source of truth for convention |
| `TwoFaceEnriched` struct | Fields like `polygon_2d: Vec<Vector2<f64>>` don't document which mathematical object they represent or cite the definition |

### 7.4 Well-Cited Sections (For Reference)

These sections properly cite sources:
- Section 1.3 (Reeb vectors): "See thesis math/05-reeb-dynamics.tex"
- Section 1.7 (Flow direction): "Proof: See thesis math/05-reeb-dynamics.tex:lem-nonlagrangian-2face"
- Section 2.7 (Simple orbits): "HK2017 Theorem 2"
- Section 3.2 (Billiard): "Rudolf 2022, Thm 4"
- Section 3.3 (HK2017): "Haim-Kislev 2017"
- Section 3.4 (Tube): "Chaidez-Hutchings 2021", "CH2021 Prop 1.10"

---

## 8. Minor Issues

1. **Typo potential:** Line 1282 comment says "p_4d" but should clarify if this is entry or exit coords
2. **Missing imports:** Code uses `Matrix2`, `Matrix4` but imports are incomplete
3. **Test fixture format:** Pentagon test (lines 2117-2135) uses different format than triangle test
4. **Undefined constant:** `EPS_UNIT` is declared but never used in any code snippet
5. **Assertion vs debug_assert inconsistency:** Some use `assert!`, some use `debug_assert!`

---

## 9. Testing Strategy Gap

The spec has test cases (§4) but the testing strategy is incomplete for robust implementation.

### 9.1 Algorithm Domain Classification

| Polytope Type | 2-Face Character | Applicable Algorithms |
|---------------|------------------|----------------------|
| Lagrangian products (K₁ × K₂) | ALL 2-faces Lagrangian | Billiard, HK2017 |
| Generic polytopes | SOME 2-faces Lagrangian | HK2017 only |
| Non-Lagrangian polytopes | NO 2-faces Lagrangian | Tube, HK2017 |

**Gap:** Spec §4.1 lists ground truth values but doesn't classify which algorithm applies to each. The 4-simplex entry is problematic:
- conv{0, e₁, e₂, e₃, e₄} has 0 on boundary, not interior
- Any 4-simplex has Lagrangian 2-faces → tube algorithm inapplicable

**Needed:** Identify a polytope with NO Lagrangian 2-faces for tube algorithm end-to-end testing.

**Candidate: Cross-polytope (hyperoctahedron)**
```
conv{±e₁, ±e₂, ±e₃, ±e₄}
```
This has 0 in its interior and 16 facets with normals proportional to (±1,±1,±1,±1). **Verify:** check that ω(n_i, n_j) ≠ 0 for all adjacent facet pairs before using as test case.

**Random polytope generation (for property-based testing):**
1. **Random V-rep:** Convex hull of N random points (e.g., uniform on sphere, or Gaussian)
   - Reject if 0 not in interior
   - Reject if any 2-face is Lagrangian (|ω(n_i, n_j)| < EPS)

2. **Random H-rep:** N random half-spaces (random unit normal, random height > 0)
   - Reject if unbounded (normals don't positively span ℝ⁴)
   - Reject if redundant (fewer than N non-redundant facets)
   - Reject if any 2-face is Lagrangian

**Caution:** "Suitable" distributions need adversarial thinking. A naive distribution might:
- Produce mostly near-Lagrangian polytopes
- Cluster normals in certain directions
- Miss edge cases the algorithm handles poorly

Consider: distributions that intentionally stress numerical precision (nearly parallel facets, nearly Lagrangian 2-faces with ω ≈ 1e-6, etc.).

### 9.2 Testing Without Ground Truth Values

Testing correctness does NOT require known capacity values. The spec should emphasize:

**Axiom tests (§4.2 exists, sufficient):**
- Scaling: c(λK) = λ²c(K)
- Monotonicity: K ⊆ L ⟹ c(K) ≤ c(L)
- Symplectomorphism invariance
- Continuity: perturb near Lagrangian → capacity changes smoothly

**Orbit validity tests (§4.3 exists, sufficient):**
- Closure, boundary, facet membership, Reeb velocity, action=period

**Internal invariant tests (§4.6 is thin, needs expansion):**

| Invariant | Test |
|-----------|------|
| Initial tube non-empty | Root tube p_start has positive area |
| Tube well-formed | Either empty or contains ≥1 trajectory |
| Combinatorics correct | Independent Reeb flow solver confirms breakpoints flow without intermediate facet hits |
| Flow map symplectic | det(A) = 1 at each extension |
| Action function correct | Trace trajectory numerically, compare summed times to action_func evaluation |

### 9.3 Continuity Near Lagrangian Products

A powerful test: take Lagrangian product with known capacity, perturb slightly to break Lagrangian structure, run tube algorithm, verify result is close to billiard result.

This tests tube algorithm on "nearly Lagrangian" polytopes where ground truth is approximately known.

### 9.4 Actionable Test Cases (Falsification Mindset)

The spec should include these concrete tests, designed to **catch bugs** not confirm correctness:

#### 9.4.1 Trivialization Tests (§1.10)

| Test | What It Falsifies |
|------|-------------------|
| `trivialize(n, untrivialize(n, v)) == v` for random v | Round-trip broken |
| `untrivialize(n, trivialize(n, w)) == w` for w ⊥ n | Inverse broken on tangent vectors |
| `ω_4D(v1, v2) == ω_2D(τ(v1), τ(v2))` for v1, v2 ⊥ n | Symplectic preservation broken |
| Near-Lagrangian: ω(n_i, n_j) = 1e-8, check τ still works | Numerical instability near degeneracy |
| n_i ≈ n_j (nearly parallel normals) | Edge case in transition matrix |

#### 9.4.2 Transition Matrix Tests (§1.11)

| Test | What It Falsifies |
|------|-------------------|
| `det(ψ) == 1` for all 2-faces | Symplecticity broken |
| `|tr(ψ)| < 2` iff `|ω(n_i, n_j)| > EPS` | Lagrangian classification inconsistent |
| `ψ_ji == ψ_ij^{-1}` | Direction dependence wrong |
| Compose ψ around a closed facet loop = identity? | Global consistency |

#### 9.4.3 Flow Map Tests (§2.10)

| Test | What It Falsifies |
|------|-------------------|
| `det(flow_map.matrix) == 1` after each extension | Area preservation broken |
| `flow_map(p)` actually lands on exit 2-face | Flow computation wrong |
| Time function gives positive time for valid flow direction | Sign error |
| Time ≈ 0: point near exit 2-face already | Edge case |
| Time very large: point far from exit 2-face | Numerical overflow |

#### 9.4.4 Tube Invariant Tests (§2.9-2.11)

| Test | What It Falsifies |
|------|-------------------|
| Root tube: `p_start.area() > 0` | Initialization wrong |
| After extension: `p_end ⊆ flow_map(p_start)` | Polygon intersection wrong |
| Empty tube: extension returns None | False positives |
| Non-empty tube: ∃ point in p_start that traces to p_end | False negatives |
| `action_func(p) == traced_action(p)` for sample points | Action function wrong |
| `rotation == Σ rotation_i` for visited 2-faces | Rotation accumulation wrong |

#### 9.4.5 Fixed Point Tests (§2.11)

| Test | What It Falsifies |
|------|-------------------|
| `flow_map(fixed_point) == fixed_point` within EPS | Fixed point computation wrong |
| `point_in_polygon(fixed_point, p_start)` | Containment test wrong |
| Fixed point on polygon edge | Boundary case |
| Near-singular: `|det(A - I)| < 1e-10` → error raised | Silent failure on degeneracy |

#### 9.4.6 4D Reconstruction Tests (§2.12-2.13)

| Test | What It Falsifies |
|------|-------------------|
| `‖breakpoints[0] - breakpoints[last]‖ < EPS` | Orbit doesn't close |
| Each breakpoint on claimed 2-face | Reconstruction wrong |
| Each segment midpoint on claimed facet | Segment leaves facet |
| `velocity_k == R_{facet_k}` | Reeb velocity wrong |
| `Σ segment_times == action_of_polygon(breakpoints)` | Action computation inconsistent |
| **Independent check:** numerically integrate Reeb flow from breakpoint[k], verify it hits breakpoint[k+1] without intermediate facet crossings | Combinatorics wrong |

#### 9.4.7 Polytope Edge Cases

| Polytope | What It Tests |
|----------|---------------|
| Tesseract [-1,1]⁴ (Lagrangian product, c=4) | Baseline, billiard works |
| Tesseract perturbed by symplectomorphism | Symplectic invariance |
| Tesseract scaled by λ=2 | Scaling axiom (c=16) |
| Tesseract perturbed to break Lagrangian structure | Tube algorithm on near-Lagrangian |
| Cross-polytope conv{±eᵢ} (**verify** no Lagrangian 2-faces first) | Tube algorithm on non-product |
| Random convex hull of 10 points (reject if 0∉int, or has Lagrangian 2-face) | Generic polytope |
| Convex hull with nearly coplanar facets | Numerical sensitivity |
| Nearly-Lagrangian: ω(n_i, n_j) ≈ 1e-6 for some 2-face | Numerical stability near degeneracy |
| Polytope with exactly 5 facets (minimum for 4D with 0 in interior?) | Minimal case |

#### 9.4.8 Algorithm Agreement Tests

| Test | What It Falsifies |
|------|-------------------|
| Lagrangian product: `billiard(K) == hk2017(K)` | Algorithm inconsistency |
| Perturbed Lagrangian: `tube(K') ≈ billiard(K)` for small perturbation | Continuity violation |
| Same polytope, different vertex enumeration order: same result | Order dependence bug |

---

## 10. Recommendations Summary

### High Priority (Truth Flow)
1. **Add citations for trivialization** (Section 1.10): τ_n definition, symplectic preservation theorem
2. **Add citations for transition matrices** (Section 1.11): ψ_F definition, trace classification theorem
3. **Add citation for rotation number formula** (Section 1.12)
4. **Add citation for "action = period"** (Section 2.5)
5. **Add citation for tube concept** (Section 2.9): reference CH2021 definition

### High Priority (Functionality)
6. Per 0.6: Replace `find_fixed_point_set` with runtime error on near-singular
7. Define `action_lower_bound` for tube pruning (min of affine func over polygon vertices)

### High Priority (Testing — per §9)
8. **Expand §4.6** with internal invariant tests: flow map det=1, action function consistency, independent Reeb flow verification
9. **Classify §4.1 ground truth** by applicable algorithm (billiard vs HK2017 vs tube)
10. **Fix or remove 4-simplex entry** — current definition invalid (0 on boundary, has Lagrangian 2-faces)
11. **Add continuity test strategy** — perturb Lagrangian products to test tube algorithm

### Medium Priority
12. Complete helper function definitions (polygon intersection, CCW sort, etc.)
13. Resolve HK2017 vs HK2019 naming inconsistency
14. Document which normal (entry/exit) is used for each trivialization

### Low Priority
15. Consolidate struct definitions
16. Establish consistent Rust code style
17. Complete test fixture code
18. Delete or mark unverified complexity claims
