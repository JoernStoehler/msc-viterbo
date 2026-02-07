# Claims Audit Notes

This document collects claims in the rust_viterbo codebase that:
1. Are non-trivial in context
2. Lack sufficient rigorous argumentation to be trusted
3. Don't reference verifiable sources where arguments can be found

---

## Priority Summary

### Critical (foundational claims the algorithm relies on)

| File | Claim | Issue |
|------|-------|-------|
| tube.rs | Reeb velocity `v_k = (2/h_k) J n_k` | Factor of 2 unverified against CH2021 |
| tube.rs | Flow map decomposes as base + time terms | Core algorithm correctness |
| tube.rs | Rotation accumulates additively | Affects pruning/closure |
| symplectic.rs | Trivialization preserves symplectic form | Crucial property, only tested empirically |
| symplectic.rs | Transition matrix formula | Central to algorithm, needs derivation |
| hk2019.rs | `c_EHZ(K) = (1/2) * [max Q(σ,β)]^{-1}` | No DOI/arXiv citation for HK2017 |
| billiard.rs | EHZ capacity = minimal billiard length | Needs precise connection to Rudolf 2022 |

### High (algorithm correctness depends on these)

| File | Claim | Issue |
|------|-------|-------|
| tube.rs | Each 2-face crossing has rotation ∈ (0, 1/2) | No runtime validation |
| hk2019.rs | Q summation uses j < i ordering | Sign depends on ordering convention |
| hk2019.rs | Factor 1/2 in capacity formula | Not derived |
| billiard_lp.rs | Adjacent edges skipping doesn't miss optimum | Unproven |
| polytope.rs | Rotation ∈ (0, 0.5) claimed but not enforced | No runtime verification |
| symplectic.rs | Rotation number = arccos(tr/2)/(2π) | Boundary behavior unclear |

### Medium (tolerance values and numerical choices)

| File | Claim | Issue |
|------|-------|-------|
| polytope.rs | EPS_FEAS=1e-10, EPS_DEDUP=1e-8, EPS_LAGR=1e-9 | No justification for hierarchy |
| tube.rs | Tolerance 1e-10 in inverse_trivialization_2face | No condition number analysis |
| billiard_lp.rs | MARGIN=0.01, SEPARATION=0.1 | Ad-hoc with no analysis |
| polygon.rs | EPS_POLY=1e-8 | No error accumulation analysis |
| hk2019.rs | Mixed tolerances (1e-8, 1e-10, 1e-12) | Inconsistent without justification |

---

## Detailed Findings by File

---

## algorithm/src/tube.rs

### Claim 1: Flow Map Reduction

**Claim:** "The key insight is that flow maps between 2-faces are affine, so tube composition reduces to 2D affine algebra."

**Location context:** Module-level documentation (line 10-11)

**Issue:** This is a non-trivial mathematical claim that reduces the problem dimensionality. While `tube-geometry-spec.md` Section 3.3 provides a sketch, the claim that composition of these affine maps remains affine (and preserves the relevant structure) needs a rigorous proof showing the composition formula is correct.

**Suggested action:** Add citation to CH2021 or thesis where affine composition of flow maps is proven.

---

### Claim 2: Rotation Range

**Claim:** "Each 2-face crossing has rotation in (0, 1/2)" (from module docstring citing CH2021 Corollary 5.3)

**Location context:** Module-level documentation (line 18)

**Issue:** The citation is provided, but the code never validates that computed rotation values fall in this range. This is a critical invariant for the algorithm's correctness.

**Suggested action:** Add runtime assertions or debug checks that `rotation ∈ (0, 0.5)` after computing each 2-face rotation in `TwoFaceData`.

---

### Claim 3: Inverse Trivialization 2-Face

**Claim:** `inverse_trivialization_2face` - "Orthonormal basis approach needs linear algebra justification" (line 148)

**Location context:** Function `inverse_trivialization_2face` (lines 149-210)

**Issue:** The comment explicitly flags this as UNCITED. The algorithm constructs an orthonormal basis {e1, e2} for the 2-face tangent space by projecting jn and kn onto the orthogonal complement of `other_normal`. The correctness relies on:
1. The projected vectors spanning the correct 2D subspace
2. The linear system in lines 195-207 correctly recovering the original 2D coordinates
3. The degenerate case handling being geometrically valid

**Suggested action:** Add a proof sketch showing that {jn_tan, kn_tan} spans T(F) when F = Ei ∩ Ej, and that the 2x2 system recovers the correct coefficients.

---

### Claim 4: Tolerance 1e-10 in inverse_trivialization_2face

**Claim:** Tolerance `1e-10` used for detecting degeneracy (lines 169, 182, 201)

**Location context:** Function `inverse_trivialization_2face`

**Issue:** Three hardcoded tolerances of `1e-10` are used without justification. These tolerances determine when vectors are considered parallel or when determinants are considered zero.

**Suggested action:** Document the expected magnitude of vectors/determinants in typical use cases, or derive the tolerance from condition number analysis.

---

### Claim 5: Time to Crossing Formula

**Claim:** "t(p) = h_k (h_j - ⟨n_j, p⟩) / (2 ω(n_k, n_j))" (line 310-311)

**Location context:** Function `compute_time_to_crossing` (lines 313-325)

**Issue:** The comment marks this as "UNCITED: needs CH2021 time formula citation". The formula assumes:
1. The Reeb velocity formula `v_k = (2/h_k) J n_k`
2. Linear flow (no curvature on facet)
3. The denominator `ω(n_k, n_j)` being nonzero (non-Lagrangian assumption)

**Suggested action:** Add citation to CH2021 (likely Section 2, around Definition 2.4-2.12) and explicitly note the non-Lagrangian precondition.

---

### Claim 6: Reeb Velocity Formula

**Claim:** "v_k = (2/h_k) J n_k" - Reeb velocity formula (line 347-349)

**Location context:** Function `compute_flow_map` (line 349)

**Issue:** Comment at line 348 marks this as "UNCITED: needs CH2021 §2.2 velocity formula". This is a foundational formula that everything else depends on. The factor of 2 is particularly important and appears in `mathematical-claims.md` Section 4.4 as "UNCITED - NEEDS VERIFICATION".

**Suggested action:** Cite the original derivation. This likely comes from the contact form λ = Σ pi dqi restricted to ∂K, giving Reeb vector field R such that dλ(R, ·) = 0 and λ(R) = 1.

---

### Claim 7: Flow Map Decomposition

**Claim:** "flow map is sum of base and time-dependent terms" (lines 388-391)

**Location context:** Function `compute_flow_map`, lines 388-391:
```rust
let total_linear = base_linear + time_linear;
let total_offset = tau_exit_delta_r + tau_exit_v_k * time_constant;
```

**Issue:** The decomposition of the flow map into a "base" linear part and a "time-dependent" linear correction is the heart of the affine flow map computation. The matrix addition `base_linear + time_linear` implicitly claims these contributions are additive, which is non-obvious.

**Suggested action:** Derive this formula explicitly from φ(p) = p + t(p)·v_k, expressing all quantities in the exit trivialization coordinates. Add reference to `tube-geometry-spec.md` Section 3.3.

---

### Claim 8: Rotation Additivity

**Claim:** Rotation accumulates additively (line 471-472)

**Location context:** Function `extend_tube_inner`, line 471-472:
```rust
let new_rotation = tube.rotation + exit_face.rotation;
```

**Issue:** The additivity of rotation in Sp̃(2) is a deep fact. While `tube-geometry-spec.md` Section 4.5 states this, the claim that individual 2-face rotations simply add is subtle. CH2021 Proposition A.4 gives bounds `ρ(B̃) ≤ ρ(ÃB̃) ≤ ρ(B̃) + 1/2` which are *consistent with* additivity but don't directly prove it.

**Suggested action:** Add precise citation. The additivity follows from the rotation homomorphism ρ: Sp̃(2) → R being a group homomorphism. Cite CH2021 §2.3 (Definition 3.17, Remark 3.18).

---

### Claim 9: Barycentric Tolerance

**Claim:** Barycentric tolerance `-0.01` for "inside triangle" test (line 256)

**Location context:** Function `reconstruct_4d_from_2d`, line 256:
```rust
if w0 >= -0.01 && w1 >= -0.01 && w2 >= -0.01 {
```

**Issue:** The tolerance `-0.01` allows points slightly outside triangles to be considered "inside". This is a 1% tolerance that has geometric consequences.

**Suggested action:** Document why this tolerance was chosen. If it's for numerical robustness, a smaller tolerance like `1e-6` might be safer.

---

### Claim 10: Degenerate Triangle Tolerance

**Claim:** Tolerance `1e-20` for degenerate triangle detection (line 298)

**Location context:** Function `barycentric_coords`, line 298

**Issue:** Extremely small tolerance for detecting degenerate (collinear) triangles. This is much smaller than machine epsilon (~2e-16), so in practice this only catches exact degeneracy.

**Suggested action:** Either use a tolerance relative to the triangle's scale (e.g., `1e-10 * max_edge_length^2`), or document that this is intentionally permissive.

---

### Claim 11: Closure Error Tolerance

**Claim:** Closure error tolerance `1e-6` (line 731)

**Location context:** Function `reconstruct_witness`, line 731

**Issue:** This tolerance determines whether an orbit "closes" properly. The choice of `1e-6` is not related to any physical scale.

**Suggested action:** Document the expected sources of closure error (numerical accumulation over many segments, floating-point trivialization roundtrips, etc.).

---

### Claim 12: Degenerate Orbit Threshold

**Claim:** Total time `< 1e-6` indicates degenerate orbit (line 737)

**Location context:** Function `reconstruct_witness`, lines 736-744

**Issue:** This rejects orbits with very small total action as "degenerate", but for small polytopes, legitimate orbits could have small action. The threshold is absolute, not relative to polytope scale.

**Suggested action:** Make the threshold relative to the polytope's scale (e.g., minimum facet height).

---

### Claim 13: Negative Segment Time Tolerance

**Claim:** Negative segment time tolerance `-1e-10` (line 748)

**Location context:** Function `reconstruct_witness`, lines 747-756

**Issue:** This allows segment times to be slightly negative (up to `-1e-10`) without rejection. Physically, negative time means the flow is going backwards.

**Suggested action:** Either use `t < 0` and handle any legitimate negative times explicitly, or document why small negative times are expected.

---

### Claim 14: Action Mismatch Warning

**Claim:** Action mismatch tolerance `1e-6` (line 639)

**Location context:** Function `solve_closed_tube`, lines 637-641

**Issue:** This checks that the action computed from `action_func.eval(fixed_point)` matches the sum of segment times. A mismatch indicates a bug. The warning is printed but the result is still returned.

**Suggested action:** Consider making this a hard error (return None) rather than a warning.

---

### Claim 15: NaN in Ord Implementation

**Claim:** Floating-point comparison in `Ord` implementation (lines 105-113)

**Location context:** `impl Ord for Tube`, lines 105-113

**Issue:** The `Ord` implementation uses `partial_cmp` on `f64` with `unwrap_or(Equal)`. NaN values are treated as equal to everything. In a priority queue, this could cause incorrect ordering.

**Suggested action:** Either assert that `action_lower_bound` is never NaN, or use `ordered_float::OrderedFloat`.

---

## algorithm/src/billiard.rs and billiard_lp.rs

### Claim 1: EHZ = Billiard Length

**Claim:** "For a Lagrangian product K = K₁ × K₂ where K₁ ⊂ ℝ²_q and K₂ ⊂ ℝ²_p, the EHZ capacity equals the minimal length of a closed K₂°-billiard trajectory in K₁."

**Location context:** Module-level documentation (lines 3-5)

**Issue:** While Rudolf 2022 Theorem 3 is cited, the claim conflates "T-length" (Minkowski length using K₂° as the norm body) with "minimal K₂°-billiard trajectory length." The precise relationship requires specifying which definition of "length" is used.

**Suggested action:** Clarify that "length" means T-length = Σᵢ h_{K₂}(dᵢ) for displacement vectors dᵢ, and cite the specific equation from Rudolf 2022.

---

### Claim 2: Lagrangian Product Detection Tolerance

**Claim:** `const EPS_LAGR_PROD: f64 = 1e-10;`

**Location context:** Line 36, tolerance for Lagrangian product detection

**Issue:** The choice of 1e-10 for distinguishing "pure q-space" vs "pure p-space" facets is arbitrary. No analysis of how numerical errors propagate.

**Suggested action:** Document the numerical analysis justifying this tolerance, or acknowledge it as an engineering choice.

---

### Claim 3: Polar Body Vertex Formula

**Claim:** "For a polygon given by {x : ⟨n_i, x⟩ ≤ h_i} with origin in interior, the polar body has vertices at n_i/h_i."

**Location context:** `Polygon2DSimple::polar()` function (lines 165-206)

**Issue:** The claim is stated as "UNCITED standard result" but requires that normals be unit vectors (not stated or enforced).

**Suggested action:** Add a citation to a convex geometry textbook (e.g., Schneider "Convex Bodies: The Brunn-Minkowski Theory"). Add assertions that normals are unit vectors.

---

### Claim 4: Angle Sorting for Boundary Order

**Claim:** "For a convex polygon with origin inside, outward normals in CCW boundary order have monotonically increasing angles."

**Location context:** `extract_lagrangian_factors` function (lines 254-257)

**Issue:** This geometric claim justifies sorting normals by `atan2(y, x)`. Only works if the polygon is strictly convex.

**Suggested action:** Add a proof sketch or citation. Add runtime assertions to detect violations.

---

### Claim 5: 2-Bounce Becomes 4-Segment Orbit

**Claim:** "A 2-bounce billiard trajectory oscillates between two points q_a, q_b ∈ ∂K₁. In the Lagrangian product K₁ × K₂, this becomes a 4-segment orbit..."

**Location context:** `construct_2bounce_witness` function (lines 364-372)

**Issue:** This orbit structure is non-trivial:
1. Why does each bounce in K₁ correspond to TWO segments in 4D?
2. The claim that p alternates between p_0 and p_1 needs derivation from Reeb flow dynamics
3. No reference to where this correspondence is established

**Suggested action:** Add a reference to the derivation in Rudolf 2022 or provide a sketch proof.

---

### Claim 6: Edge Margin Constant

**Claim:** `const MARGIN: f64 = 0.01;` - "Using 0.01 means we exclude the outer 1% of each edge."

**Location context:** Lines 40-44 in billiard_lp.rs

**Issue:** The 1% margin is described as preventing "degenerate vertex bounces" but:
1. No proof that 1% is sufficient to avoid numerical issues
2. No analysis of how this affects optimality

**Suggested action:** Either prove that optimal solutions never occur at vertex bounces, or acknowledge this as an approximation with quantified error bounds.

---

### Claim 7: Separation Constant

**Claim:** `const SEPARATION: f64 = 0.1;` - "This ensures the bounce points don't both approach the shared vertex."

**Location context:** Lines 46-50 in billiard_lp.rs

**Issue:** The 10% separation constraint for adjacent edges is ad-hoc with no mathematical justification.

**Suggested action:** Justify this value or acknowledge it as a heuristic.

---

### Claim 8: LP Epigraph Reformulation

**Claim:** "z₁ ≥ ⟨d₁₂, yₗ⟩ for all vertices yₗ of K₂" reformulates support function minimization

**Location context:** `solve_3bounce_lp` function (lines 143-183)

**Issue:** The epigraph reformulation claims that `min z` subject to `z ≥ ⟨d, y⟩ for all y ∈ vertices(K₂)` equals `h_{K₂}(d)`. The code comment on line 143 acknowledges this is uncited.

**Suggested action:** Add a citation (e.g., Boyd & Vandenberghe "Convex Optimization" §4.2.5).

---

### Claim 9: Adjacent Edges Give Degenerate 2-Bounce

**Claim:** "Only considers NON-ADJACENT edge pairs, since adjacent edges share a vertex and the LP would find a degenerate solution with d₁₂ = 0."

**Location context:** `find_min_2bounce_lp` function (lines 427-429)

**Issue:** The claim that adjacent edges always yield d₁₂ = 0 is incorrect in general. Two bounces on adjacent edges could produce a valid trajectory if bounce points are not at the shared vertex.

**Suggested action:** Either prove that for 2-bounce trajectories adjacent-edge configurations are always suboptimal, or add MARGIN/SEPARATION constraints and include adjacent edges.

---

### Claim 10: Triangle Capacity Value

**Claim:** "Triangle × Triangle capacity is 1.5 (NOT 2.25 as the Fagnano orbit gives)"

**Location context:** Test `test_lp_triangle_capacity` (lines 752-755)

**Issue:** This asserts a specific mathematical value (1.5) without citation or derivation.

**Suggested action:** Add a citation for the 1.5 value or mark as conjectured/computed.

---

## algorithm/src/hk2019.rs

### Claim 1: Capacity Formula

**Claim:** "c_EHZ(K) = (1/2) * [max_{σ∈S_F, β∈M(K)} Q(σ,β)]^{-1}"

**Location context:** Module documentation (lines 41-46) and `compute_hk2019_capacity_with_timeout` (line 367)

**Issue:** The formula is attributed to "HK2017 Theorem 1" with an internal file reference `HK2017-EHZ-polytopes.tex, lines 68-78`. No DOI, arXiv ID, or standard bibliographic citation is provided.

**Suggested action:** Add proper bibliographic citation with DOI/arXiv ID. If unpublished, state that explicitly and include the theorem statement in full.

---

### Claim 2: Tesseract Capacity = 4

**Claim:** "For tesseract, capacity should be 4"

**Location context:** Test `tesseract_hk2019_capacity` (lines 515-519)

**Issue:** The expected capacity value 4 for the 4D hypercube is asserted without reference. The test uses a loose tolerance (0.5).

**Suggested action:** Cite a reference establishing c_EHZ(tesseract) = 4, or mark as conjectured/computed.

---

### Claim 3: Tesseract Optimal Configuration

**Claim:** "Optimal: β = (0.25, 0.25, 0, 0, 0.25, 0.25, 0, 0) with permutation σ = [0, 5, 1, 4, 2, 3, 6, 7] gives Q = 0.125"

**Location context:** Test `tesseract_optimal_q_value` (lines 576-594)

**Issue:** A specific optimal configuration is asserted without derivation. How was this found? Why is it optimal?

**Suggested action:** Either prove optimality, cite the source, or relabel as "known good configuration".

---

### Claim 4: Q Summation Ordering

**Claim:** "Q(σ,β) = Σ_{j<i} β_{σ(i)} β_{σ(j)} ω(n_{σ(i)}, n_{σ(j)})"

**Location context:** Module documentation (line 45) and `compute_q` (lines 70-71)

**Issue:** The summation uses j < i (lower triangular), which is asymmetric. Since ω is antisymmetric, the ordering choice affects the sign of Q. No explanation of why this ordering is correct.

**Suggested action:** Explain why j<i ordering produces the correct Q value. Reference the specific justification in HK2017.

---

### Claim 5: Constraint Set M(K)

**Claim:** "M(K) = {β_i ≥ 0, Σ β_i h_i = 1, Σ β_i n_i = 0}"

**Location context:** Module documentation (line 46) and `solve_qp_for_permutation` (lines 102-104)

**Issue:** The constraint set is stated without derivation. Why use Σ β_i h_i = 1 for normalization? Why does Σ β_i n_i = 0 encode orbit closure?

**Suggested action:** Add brief explanation of what β_i represent physically and why these constraints encode closed orbits.

---

### Claim 6: Factor 1/2 in Capacity

**Claim:** "capacity = 0.5 / max_q"

**Location context:** `compute_hk2019_capacity_with_timeout` (line 446)

**Issue:** The factor 1/2 is not derived. Is it a convention, normalization choice, or from the symplectic form definition?

**Suggested action:** Explain where factor 1/2 comes from. Reference the specific equation in HK2017.

---

### Claim 7: Segment Times Formula

**Claim:** "segment_times = beta.iter().map(|b| b * total_time).collect()"

**Location context:** `compute_hk2019_capacity_with_timeout` (lines 451-457)

**Issue:** The formula `segment_time_i = β_i * capacity` is stated without derivation.

**Suggested action:** Add derivation or reference. If conjectural/approximate, mark clearly.

---

### Claim 8: Indefinite Quadratic

**Claim:** "For indefinite quadratics (which the symplectic form produces), the global maximum can lie on 2D or higher-dimensional faces."

**Location context:** Module warning (lines 10-12) and `solve_qp_for_permutation` (lines 94, 106-108)

**Issue:** There is no proof that the symplectic form actually produces an indefinite quadratic Q.

**Suggested action:** Add brief argument showing the Hessian of Q has both positive and negative eigenvalues.

---

### Claim 9: Feasible Region is Bounded

**Claim:** "The feasible region is a polytope."

**Location context:** `solve_qp_for_permutation` (line 106)

**Issue:** For the algorithm to work, M(K) must be bounded. Boundedness is asserted but not proven.

**Suggested action:** Add proof or reference. This likely follows from β_i ≥ 0 combined with Σ β_i h_i = 1 when all h_i > 0.

---

### Claim 10: Vertex Enumeration by Subsets

**Claim:** Vertex enumeration by iterating over subsets of size ≤ 5

**Location context:** `solve_qp_for_permutation` (lines 152-153)

**Issue:** Assumes vertices correspond to basic feasible solutions with at most 5 non-zero components. Correct for non-degenerate polytopes, but degeneracy can cause issues.

**Suggested action:** Add note explaining the LP theory and how degeneracy is handled.

---

### Claim 11: Simplex Normal Magnitude

**Claim:** Simplex normal "(-1,-1,-1,-1)/√2"

**Location context:** Test `simplex_5` (lines 537-538)

**Issue:** The magnitude of (-1,-1,-1,-1) is √4 = 2, not √2. The normalization `/2.0_f64.sqrt()` gives magnitude √2 ≠ 1.

**Suggested action:** Verify normalization is correct (should be /2.0 for unit vector).

---

## algorithm/src/polygon.rs

### Claim 1: EPS_POLY Tolerance

**Claim:** `const EPS_POLY: f64 = 1e-8;`

**Location context:** Module-level constant

**Issue:** The tolerance value 1e-8 is stated without justification for why this specific value is appropriate.

**Suggested action:** Add analysis showing expected floating-point error magnitude after typical transformation chains.

---

### Claim 2: Polygon Emptiness

**Claim:** `fn is_empty(&self) -> bool { self.vertices.len() < 3 }`

**Location context:** `Polygon2D::is_empty()` method

**Issue:** This conflates two concepts: a polygon with too few vertices and an "infeasible region". A degenerate polygon (3+ collinear vertices) could pass this check.

**Suggested action:** Either rename to clarify this checks vertex count, or add a proper degeneracy check.

---

### Claim 3: Affine Minimum at Vertices

**Claim:** `pub fn minimize(&self, func: &AffineFunc) -> Option<(f64, Vector2f)>` iterates only over vertices.

**Location context:** `Polygon2D::minimize()` method

**Issue:** The implicit claim is that for a convex polygon, the minimum of an affine function occurs at a vertex. While standard, it's not stated or cited.

**Suggested action:** Add a comment citing the LP vertex theorem.

---

### Claim 4: Sutherland-Hodgman

**Claim:** "Compute intersection using Sutherland-Hodgman algorithm."

**Location context:** `Polygon2D::intersect()` method

**Issue:** The algorithm is named but not cited. Sutherland-Hodgman clips against a **convex** clipping polygon only. The code assumes `other` is convex but doesn't document or verify this.

**Suggested action:** Add citation for Sutherland-Hodgman and document the convexity assumption.

---

## algorithm/src/polytope.rs

### Claim 1: Three Epsilon Values

**Claim:**
```rust
pub const EPS_FEAS: f64 = 1e-10;
pub const EPS_DEDUP: f64 = 1e-8;
pub const EPS_LAGR: f64 = 1e-9;
```

**Location context:** Module-level constants

**Issue:** Three different epsilon values are used without justification for why they differ.

**Suggested action:** Add comments explaining why three different tolerances are needed and how each value was chosen.

---

### Claim 2: Flow Direction from ω Sign

**Claim:** "if ω(nᵢ, nⱼ) > 0, flow crosses from Eᵢ into Eⱼ"

**Location context:** `FlowDir` enum documentation

**Issue:** While the citation "CH2021 §2.2" is given, the mathematical reasoning is not reproduced. The normalization convention for facet normals affects this.

**Suggested action:** Add a brief mathematical note explaining the normal convention and why the symplectic form sign determines flow direction.

---

### Claim 3: Rotation Range Not Enforced

**Claim:** `pub rotation: f64,` with comment "Rotation increment ρ(F) ∈ (0, 0.5) in turns."

**Location context:** `TwoFaceData` struct

**Issue:** The claim is cited but the code doesn't verify or enforce this constraint.

**Suggested action:** Add a debug assertion that the computed rotation is in (0, 0.5).

---

### Claim 4: Tesseract 8 Non-Lagrangian Faces

**Claim:** Test assertion: `data.two_faces.len(), 8, "tesseract should have exactly 8 non-Lagrangian 2-faces"`

**Location context:** Test `lagrangian_detection_uses_adjacent_faces()`

**Issue:** The comment says "q-facet meets p-facet = 4×4 = 16 pairs / 2 (symmetry) = 8" but this arithmetic is wrong.

**Suggested action:** Verify the expected count. Reconcile this with the test expecting 8.

---

## algorithm/src/affine.rs

### Claim 1: 4D to 2D Reduction

**Claim:** "The tube algorithm reduces 4D flow maps to 2D affine maps via trivialization."

**Location context:** Module-level docstring (lines 1-5)

**Issue:** This is a high-level architectural claim. The reference "See thesis §4.3" is given but §4.3 does not exist yet.

**Suggested action:** Either complete thesis §4.3, or cite CH2021 Section 2 and tube-geometry-spec.md Section 3.3 directly.

---

### Claim 2: Composition Formula

**Claim:** "(self ∘ other)(x) = self(other(x)) = A1(A2*x + b2) + b1" leads to "linear: self.linear * other.linear"

**Location context:** `AffineMap2D::compose` method (lines 38-44)

**Issue:** While elementary algebra, the formula is stated without explicit verification. For critical code, even simple formulas deserve explicit verification.

**Suggested action:** Add inline comment showing the derivation.

---

### Claim 3: Fixed Point and Closed Orbits

**Claim:** "Fixed point: x = Ax + b => (I - A)x = b"

**Location context:** `AffineMap2D::fixed_point` method (lines 46-54)

**Issue:** The connection to "closed Reeb orbits" mentioned in line 49 is a significant geometric claim that isn't justified.

**Suggested action:** Add citation to CH2021 Definition 3.12 which states "periodic orbit = cycle with fixed point of φ_p".

---

### Claim 4: Action is Affine

**Claim:** "The action is affine in the starting point coordinates."

**Location context:** `AffineFunc` struct docstring (lines 57-60)

**Issue:** This claim that action accumulates as an affine function is foundational to the algorithm's efficiency but not cited.

**Suggested action:** Add citation to tube-geometry-spec.md §3.4.

---

### Claim 5: Gradient Transform

**Claim:** "(f ∘ φ)(x) = f(φ(x))" leads to "gradient: map.linear.transpose() * self.gradient"

**Location context:** `AffineFunc::compose` method (lines 84-90)

**Issue:** The transpose formula is critical for action computation and should be explicitly documented.

**Suggested action:** Add inline comment showing the derivation: `// g·(Ax + b) + c = (Aᵀg)·x + (g·b + c)`.

---

## geom/src/symplectic.rs

### Claim 1: Quaternion Identification

**Claim:** "Quaternion relations i² = j² = k² = -I" and "identification of quaternion i with almost complex structure J"

**Location context:** Module `quaternion` docstring (lines 15-17)

**Issue:** The quaternion matrices are defined but:
1. No proof that they satisfy quaternion relations
2. The identification i = J connects two different mathematical structures without explanation

**Suggested action:** Cite standard reference and explain the identification.

---

### Claim 2: Symplectic Form Definition

**Claim:** "ω(x,y) = ⟨Jx, y⟩" is the standard symplectic form

**Location context:** `symplectic_form` function (lines 62-66)

**Issue:** This connects the symplectic form to the almost complex structure in a specific way that depends on coordinate conventions.

**Suggested action:** Cite standard reference and verify consistency with coordinate convention.

---

### Claim 3: Trivialization Formula

**Claim:** "τ_n: maps V ∈ ℝ⁴ to (⟨V, jn⟩, ⟨V, kn⟩) ∈ ℝ²"

**Location context:** `trivialization` function (lines 73-82)

**Issue:** This trivialization formula is stated without proof that:
1. It actually trivializes the contact structure
2. It preserves the symplectic form
3. The choice of j, k matrices is canonical

**Suggested action:** Add citation to CH2021 or thesis. Explain why jn and kn form a symplectic basis for the contact plane.

---

### Claim 4: Transition Matrix Formula

**Claim:** "ψ = τ_n₂ ∘ (τ_n₁)⁻¹ formula needs proof reference"

**Location context:** `transition_matrix` function (lines 84-105)

**Issue:** The explicit matrix formula is presented without derivation. This is the key formula connecting trivializations across facets.

**Suggested action:** Add derivation or cite CH2021.

---

### Claim 5: Sp(2) Classification

**Claim:** The classification PositiveHyperbolic (Tr > 2), PositiveShear (Tr = 2), etc.

**Location context:** `Sp2Class` enum (lines 107-118)

**Issue:** The classification is stated without proof. Boundary cases (Tr = ±2) need careful handling.

**Suggested action:** Cite standard reference on SL(2,ℝ) ≅ Sp(2) classification.

---

### Claim 6: Rotation Number Formula

**Claim:** "θ = arccos(tr/2)/(2π) for elliptic matrices"

**Location context:** `rotation_number` function (lines 149-164)

**Issue:** The formula gives the rotation angle for a positive elliptic matrix. However:
1. arccos returns values in [0, π], giving θ ∈ [0, 0.5]
2. No handling of the case θ = 0.5 (half-turn)

**Suggested action:** Add citation and clarify boundary behavior.

---

### Claim 7: 2-Face Rotation

**Claim:** "Rotation increment for a 2-face with given normals" using CH2021 Corollary 5.3

**Location context:** `two_face_rotation` function (lines 166-181)

**Issue:** The function computes rotation number of the transition matrix as the "rotation increment". No proof that ψ is always positive elliptic for non-Lagrangian 2-faces.

**Suggested action:** Add citation to CH2021 Corollary 5.3 and explanation of the connection.

---

## geom/src/polytope.rs

### Claim 1: 2-Face Definition

**Claim:** "A 2-face is the intersection of two facets Fᵢ ∩ Fⱼ."

**Location context:** Module-level docstring (line 6)

**Issue:** This implicitly assumes "simple" polytopes. For non-simple polytopes, facet intersections may have smaller dimension.

**Suggested action:** Add citation to standard polytope theory and document the simplicity assumption.

---

### Claim 2: Vertex Enumeration Algorithm

**Claim:** The `two_faces` algorithm (lines 153-195) enumerates all 2-faces by iterating over all pairs of facets.

**Location context:** `PolytopeHRep::two_faces` method

**Issue:** This algorithm assumes:
1. Every vertex is the intersection of exactly 4 hyperplanes
2. The enumeration catches all vertices
3. Degenerate vertices are not handled

**Suggested action:** Document the simplicity assumption explicitly, or prove correctness for general polytopes.

---

### Claim 3: Tesseract Has 24 2-Faces

**Claim:** "Tesseract has 24 2-faces" (line 358)

**Location context:** Test `two_faces_for_tesseract`

**Issue:** This is a verifiable combinatorial fact, but stated without derivation.

**Suggested action:** Add a brief justification of the f-vector.

---

### Claim 4: Vertex Ordering Algorithm

**Claim:** The cyclic ordering algorithm using `atan2` correctly orders face vertices.

**Location context:** `order_face_vertices` function (lines 261-289)

**Issue:** The algorithm projects vertices to the 2-face plane and orders by angle. No proof that the constructed basis spans the 2-face plane.

**Suggested action:** Add citation to computational geometry text and proof sketch.

---

## geom/src/perturbation.rs

### Claim 1: Lagrangian Singularity

**Claim:** "Lagrangian 2-faces are problematic for the algorithm because the transition matrix is singular."

**Location context:** Module docstring (lines 3-5)

**Issue:** The claim that the transition matrix is singular for Lagrangian 2-faces needs justification.

**Suggested action:** Add explanation: when ω(n₁, n₂) = 0, the trivializations are related in a degenerate way.

---

### Claim 2: Perturbation Validity

**Claim:** The perturbation strategy `perturb_polytope_normals` produces a valid polytope.

**Location context:** `perturb_polytope_normals` function (lines 88-128)

**Issue:** The perturbation adds random vectors to normals but:
1. No guarantee the perturbed polytope is still convex
2. No analysis of geometric distortion
3. Probabilistic elimination of Lagrangian 2-faces not proven

**Suggested action:** Document assumptions: for small ε, the perturbed polytope is combinatorially equivalent; generically, random perturbations avoid Lagrangian 2-faces.

---

## ffi/src/lib.rs

### Claim 1: Coordinate Convention

**Claim:** "normals: List of unit outward normals, each as [f64; 4]"

**Location context:** `tube_capacity_hrep` function docstring (line 104)

**Issue:** The FFI layer assumes a specific ordering convention for the 4D coordinates but the mapping between array indices and symplectic coordinates is implicit.

**Suggested action:** Document the explicit coordinate convention: "coordinates are ordered as (q₁, q₂, p₁, p₂)".

---

### Claim 2: Billiard Theorem

**Claim:** "This algorithm only works for Lagrangian products K = K₁ × K₂. The capacity equals the minimal length of a closed K₂°-billiard in K₁."

**Location context:** `billiard_capacity_hrep` function docstring (lines 147-148)

**Issue:** This is a non-trivial theorem from symplectic geometry requiring a citation.

**Suggested action:** Add a citation to the source theorem (Artstein-Avidan, Milman, Ostrover).

---

### Claim 3: HK2019 Complexity

**Claim:** "This algorithm works for any 4D polytope but has O(F!) complexity in the number of facets."

**Location context:** `hk2019_capacity_hrep` function docstring (lines 200-201)

**Issue:** The O(F!) complexity claim is stated without citation.

**Suggested action:** Add citation to Haim-Kislev 2019 paper with section reference for the complexity analysis.

---

## optim/src/lib.rs

### Claim 1: Indefinite Quadratic

**Claim:** "Q is an **indefinite quadratic** (zero diagonal, off-diagonal = symplectic form values)."

**Location context:** Module-level documentation (line 14)

**Issue:** The claim that Q is indefinite is stated as fact but not justified.

**Suggested action:** Provide a proof sketch or reference showing Q is genuinely indefinite.

---

### Claim 2: OSQP Limitation

**Claim:** "Standard convex QP solvers (OSQP) cannot help because they require PSD objectives."

**Location context:** Module-level documentation (line 15)

**Issue:** This is partially correct but oversimplified. The claim doesn't address reformulations or the NSD case.

**Suggested action:** Clarify this refers to direct application without reformulation.

---

### Claim 3: KKT Enumeration

**Claim:** "If indefinite: implement complete KKT enumeration over all faces"

**Location context:** Implementation plan in module documentation (line 26)

**Issue:** The correctness of KKT enumeration for non-convex QP needs a reference.

**Suggested action:** Add a reference to the theory of non-convex QP over polytopes.

---

### Claim 4: Quadratic Form Notation

**Claim:** "Maximize Q(β) = Σ_{j<i} β_i β_j c_{ij}"

**Location context:** Problem statement in module documentation (line 9)

**Issue:** The relationship to the Hessian matrix representation needs clarification. Factor of 2 relationship is not documented.

**Suggested action:** Clarify whether H has entries h_{ij} = c_{ij}/2 or whether c_{ij} should be doubled.

---

## Summary Statistics

| Category | Count |
|----------|-------|
| Critical (foundational) | 7 |
| High (algorithm correctness) | 6 |
| Medium (tolerances/numerics) | 15 |
| Citations needed | 25+ |
| Derivations needed | 15+ |
| Total claims identified | 70+ |

---

## Recommended Priority Actions

1. **Add CH2021 citations** for Reeb velocity formula, rotation bounds, and flow direction
2. **Verify factor of 2** in Reeb velocity formula against original source
3. **Add runtime assertions** for rotation ∈ (0, 0.5) invariant
4. **Document tolerance choices** with condition number analysis or empirical justification
5. **Prove or cite** the billiard-capacity correspondence for Lagrangian products
6. **Add arXiv/DOI** for HK2017 theorem reference
