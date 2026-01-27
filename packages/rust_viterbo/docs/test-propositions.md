# Mathematical Propositions for Unit Testing

> **⚠️ PARTIALLY STALE** — Many test case statuses (✗ BROKEN, etc.) refer to the deleted v0.1.0 implementation.
> The mathematical propositions remain valid; the test-to-code mappings need updating for current crates.

> **Note:** This is a detailed reference document. For quick navigation:
> - Mathematical claims with citations: see `mathematical-claims.md`
> - Test infrastructure and running tests: see `test-interpretation.md` (archived)
> - Test case catalog: see `test-cases.md`

This document lists mathematical propositions that unit tests should verify.

**Purpose:** Each proposition is a mathematical fact that, if violated by our algorithms, indicates a bug. Failing tests EXPOSE problems; passing tests BUILD CONFIDENCE.

**Citation Convention:** Each proposition cites its source. "Folklore" means standard textbook material. Claims without citations are SUSPECT and need verification.

---

## 0. Polytope Classification

Before testing capacity, we must understand what properties of polytopes affect algorithm behavior.

### 0.1 Dimension and Facet Count

| Property | Symbol | Affects |
|----------|--------|---------|
| Ambient dimension | 2n (we use n=2, so 4D) | All algorithms |
| Facet count | F | HK2019 complexity O(F!), Billiard O(F²) |
| Vertex count | V | Dual representation |

**Test implication:** Verify algorithms handle various facet counts (test polytopes with F from 5 up to algorithm limits).

**Implementation status:**
| Facet count | Polytope tested | File |
|-------------|-----------------|------|
| F=5 | 4-simplex | ✗ Not tested |
| F=6 | Triangle×Triangle | ✗ BROKEN (fixture wrong) |
| F=8 | Tesseract, Rectangle | ✓ capacity_known_values.rs |
| F=10 | Pentagon×Pentagon | ✗ BROKEN (fixture wrong) |
| F=12 | Hexagon×Hexagon | ✗ Not implemented |
| F=16 | 16-cell | ✗ Not implemented |

### 0.2 Lagrangian Product Structure

**Definition:** K ⊂ ℝ⁴ is a Lagrangian product if K = K₁ × K₂ where K₁ ⊂ ℝ²_q and K₂ ⊂ ℝ²_p.

**Detection:** All facet normals have form (n_q, 0) or (0, n_p).

**Why it matters:**
- Billiard algorithm: ONLY works for Lagrangian products (Rudolf 2022)
- HK2019: Works for all convex polytopes
- Tube algorithm: Requires non-Lagrangian 2-faces (CH2021)

| Polytope | Lagrangian? | Billiard | HK2019 | Tube |
|----------|-------------|----------|--------|------|
| Tesseract | Yes (□×□) | ✓ | ✓ | Fails |
| Triangle×Triangle | Yes | ✓ | ✓ | Fails |
| Pentagon×Pentagon | Yes | ✓ | Timeout | Fails |
| 4-simplex | No | N/A | ✓ | ? |
| 16-cell | No | N/A | ✓ | ? |
| Perturbed tesseract | No | N/A | ✓ | ✓ |

**Implementation status:**
| Test | File | Status |
|------|------|--------|
| Lagrangian detection | lagrangian_product.rs | ✓ `is_lagrangian_product` |
| Billiard rejects non-Lagrangian | Not tested | ✗ |
| HK2019 works on all polytopes | algorithm_agreement.rs | Partial (random products only) |
| Tube fails on Lagrangian | tube_algorithm.rs | ✓ `tube_fails_on_tesseract` |

### 0.3 Symmetry Group

| Polytope | Symmetry | Impact |
|----------|----------|--------|
| Tesseract | B₄ (hyperoctahedral) | Many degenerate optima |
| Regular n-gon × same | Dₙ × Dₙ | Degenerate optimal orbits |
| K × K (same polygon) | At least S₂ (swap) | Symmetric optima |
| K × T (rotated) | Reduced | Unique optimum? |

**Test implications:**
1. **Symmetric polytopes may trigger degenerate algorithm behavior.** Multiple optimal orbits exist; algorithm must handle ties correctly. Numerical instability possible when optima coincide.
2. **Non-symmetric polytopes have unique optima.** These are cleaner test cases for verifying correctness.
3. **MUST test BOTH:** Symmetric cases (tesseract, K×K) expose degeneracy handling bugs. Non-symmetric cases (K×T rotated, random perturbations) expose correctness bugs without degeneracy masking them.

**Implementation status:**
| Test case | Symmetric? | Implemented? | File |
|-----------|------------|--------------|------|
| Tesseract | Yes (B₄) | ✓ | capacity_known_values.rs |
| Triangle×Triangle | Yes (D₃×D₃) | ✗ BROKEN | capacity_known_values.rs (fixture wrong) |
| Pentagon×Pentagon rotated | No (reduced) | ✗ BROKEN | capacity_known_values.rs (fixture wrong) |
| Rectangle 2×1 | Yes (D₂×D₂) | ✓ | capacity_known_values.rs |
| Random Lagrangian products | Varies | ✓ | algorithm_agreement.rs (proptest) |
| Perturbed tesseract | No | Partial | tube_algorithm.rs |

### 0.4 2-Face Types

For each pair of facets (i, j), the 2-face F_ij has type:
- **Lagrangian:** ω(n_i, n_j) = 0 (normals symplectically orthogonal)
- **Non-Lagrangian:** ω(n_i, n_j) ≠ 0 (flow crosses this face)

**Source:** CH2021, Definition 3.3

**Test:** For Lagrangian products, SOME 2-faces are Lagrangian (but not necessarily all). For example, the tesseract has 20 Lagrangian and 8 non-Lagrangian 2-faces.

---

## 1. Capacity Axioms

### 1.1 Scaling: c(λK) = λ²c(K)

**Statement:** For any convex body K ⊂ ℝ⁴ and λ > 0:
```
c(λK) = λ² · c(K)
```

**Source:** Ekeland-Hofer 1989, Axiom (iii); Hofer-Zehnder 1994, Theorem 3.

**Why quadratic:** Action = ∮ p dq has units of [length]², hence scales as λ².

**Test:** Compute c(K), c(2K). Verify c(2K) = 4·c(K).

| Polytope | c(K) | c(2K) | Expected | Status |
|----------|------|-------|----------|--------|
| Tesseract | 4.0 | 16.0 | 16.0 | ✓ |
| Triangle×Triangle | 1.5 | 6.0 | 6.0 | ✗ (fixture broken) |
| Pentagon×Pentagon | 3.441 | 13.764 | 13.764 | ✗ (fixture broken) |

**Failure indicates:** Fundamental algorithm bug or wrong height-to-capacity formula.

### 1.2 Monotonicity: K ⊆ L ⟹ c(K) ≤ c(L)

**Statement:** If K ⊆ L (as sets), then c(K) ≤ c(L).

**Source:** Ekeland-Hofer 1989, Axiom (ii); follows from infimum definition.

**Test:** Create K ⊂ L (e.g., K = tesseract, L = 1.5×tesseract). Verify c(K) ≤ c(L).

**Failure indicates:** Algorithm not finding true minimum, or wrong feasible set.

### 1.3 Symplectomorphism Invariance: c(AK) = c(K) for A ∈ Sp(4)

**Statement:** For any A ∈ Sp(4,ℝ) and convex K:
```
c(AK) = c(K)
```

**Source:** Ekeland-Hofer 1989, Axiom (i); Gromov 1985 non-squeezing.

**CRITICAL:** The group Sp(4,ℝ) is 10-dimensional. Testing ONE rotation is NOT sufficient.

**Full Sp(4) parametrization:**
```
Sp(4,ℝ) = {A ∈ GL(4,ℝ) : AᵀJA = J}

where J = [0  I₂]
          [-I₂ 0]
```

**Generators of Sp(4):**
1. **Block-diagonal rotations:** R(θ) ⊕ R(φ) in (q₁,p₁) and (q₂,p₂) planes
2. **Shears:** maps like (q,p) ↦ (q, p + Sq) for symmetric S
3. **Symplectic exchange:** swapping q₁↔q₂ with p₁↔p₂

**Minimal test set for invariance:**
| Transform | Matrix | Type |
|-----------|--------|------|
| R(θ) ⊕ I₂ | Block rotation in (q₁,p₁) | Partial rotation |
| I₂ ⊕ R(φ) | Block rotation in (q₂,p₂) | Partial rotation |
| R(θ) ⊕ R(θ) | Same angle both blocks | Diagonal rotation |
| Shear S₁ | (q,p) ↦ (q, p+Sq) | Upper triangular |
| Symplectic swap | q₁↔q₂, p₁↔p₂ | Permutation |
| Random A ∈ Sp(4) | Via Iwasawa decomposition | Full class |

**Test:** For each transform type, verify |c(AK) - c(K)| < ε.

**NOT CURRENTLY TESTED.** This is a critical gap.

### 1.4 Conformality: c(B⁴) = π, c(Z⁴) = π

**Statement:**
```
c(B⁴(1)) = π      (unit ball)
c(Z⁴(1)) = π      (cylinder B²(1) × ℝ²)
```

**Source:** Gromov 1985; Hofer-Zehnder 1994, Theorem 1.

**Note:** These are smooth bodies, not polytopes. For polytopes:
```
c(Pₙ × Pₙ) → π·r²  as n → ∞
```
where Pₙ is regular n-gon with circumradius r.

**Test:** Verify convergence sequence for n = 4, 6, 8, 12, 24.

---

## 2. Known Capacity Values

Each value below is a GROUND TRUTH that tests must verify.

### 2.1 Tesseract: c([-1,1]⁴) = 4.0

**Statement:**
```
c_EHZ([-1,1]⁴) = 4.0
```

**Source:** Haim-Kislev 2019, Example 4.6; Rudolf 2022, Example 3.5

**Derivation:** For □² × □² where □² = [-1,1]², optimal orbit bounces along x₁=±1, x₃=±1 faces with period 4.

**Tested:** ✓

### 2.2 Triangle × Triangle: c = 1.5 r²

**Statement:** For equilateral triangle T with circumradius r:
```
c_EHZ(T × T) = 1.5 · r²
```

For r=1: c = 1.5

**Source:** Verified computationally (HK2019 and billiard LP agree). No closed-form publication found.

**IMPORTANT:** The Fagnano orbit (edge midpoints) gives T-length 2.25, but this is NOT optimal. The Minkowski-optimal orbit hits edges at t=1/3, giving T-length 1.5.

**Reference:** archive/billiard-correctness-proof.md, Section 9

**Tested:** Verified - Billiard (LP) and HK2019 both return 1.5.

### 2.3 Pentagon × Rotated Pentagon: c ≈ 3.441

**Statement:** For regular pentagon K with circumradius 1, and T = K rotated by 90°:
```
c_EHZ(K × T) = 2·cos(π/10)·(1 + cos(π/5)) ≈ 3.4409548011...
```

**Exact formula:**
```
c = (√5 + 1)/2 · (1 + (√5 + 1)/4) = φ · (1 + φ/2)
```
where φ = golden ratio

**Source:** Haim-Kislev & Ostrover 2024, Proposition 1

**Significance:** This is a COUNTEREXAMPLE to Viterbo's conjecture. The systolic ratio exceeds 1:
```
ρ = c² / (2·Vol) = (√5 + 3) / 5 ≈ 1.0472
```

**Tested:** ✗ (fixture returns 2.127, expected 3.441)

### 2.4 Standard Simplex in ℝ⁴: c = ?

**Statement:** For the standard 4-simplex Δ⁴ = conv{0, e₁, e₂, e₃, e₄}:
```
c_EHZ(Δ⁴) = ??? (NEEDS VERIFICATION)
```

**Claimed source:** Haim-Kislev thesis (2019), Siegel's Symplectic Capacities Project

**WARNING:** The formula c = 1/(2n) = 0.25 needs citation verification. The simplex is NOT a Lagrangian product, so billiard algorithm cannot be used. Only HK2019 applies.

**Tested:** ✗

### 2.5 Rectangle Products

**Statement:** For rectangle R(a,b) = [-a,a] × [-b,b] with a ≥ b:
```
c_EHZ(R(a,b) × R(a,b)) = 4·min(a,b)² = 4b²
```

**Source:** Direct computation; special case of tesseract when a=b=1.

| Dimensions | Capacity | Status |
|------------|----------|--------|
| 1×1 × 1×1 (tesseract) | 4.0 | ✓ Tested |
| 1×0.5 × 1×0.5 | 1.0 | ✓ Tested |
| 2×0.5 × 2×0.5 | 1.0 | Not tested |
| 2×1 × 2×1 | 4.0 | Not tested |

**Failure indicates:** Scaling or width formula wrong.

### 2.6 Cross-Polytope (16-cell): c = ?

**Statement:** For the 16-cell (dual of tesseract):
```
c_EHZ(16-cell) = ??? (UNKNOWN)
```

**Note:** 16-cell is NOT a Lagrangian product. Only HK2019 applies.

**Conjecture:** c(tesseract) · c(16-cell) ≥ 4? (capacity-volume analog of Mahler)

**Tested:** ✗

### 2.7 24-cell: c = ?

**Statement:** For the 24-cell (self-dual regular 4-polytope):
```
c_EHZ(24-cell) = ??? (UNKNOWN)
```

**Note:** More "spherical" than tesseract. Interesting test case for tube algorithm.

**Tested:** ✗

---

## 3. Algorithm-Specific Claims

Each algorithm has its own correctness criteria beyond just "same capacity value."

### 3.1 Billiard Algorithm (Rudolf 2022)

**Applicability:** Lagrangian products K₁ × K₂ only.

**Main theorem:** For K₁ ⊂ ℝ² convex polygon:
```
c_EHZ(K₁ × K₂) = min T-length of (K₁, K₂°)-Minkowski billiard
```

**Source:** Rudolf 2022, Theorem 1

**3.1.1 Bounce count bound**

**Statement:** Optimal trajectory has at most n+1 bounces where n = dim(K₁).
For 2D polygons: ≤ 3 bounces.

**Source:** Rudolf 2022, Theorem 4

**Test:** Verify algorithm considers 2-bounce and 3-bounce; verify optimal never exceeds 3.

**Failure indicates:** Missing orbit candidates.

**3.1.2 LP solution is global minimum**

**Statement:** Linear programming formulation finds GLOBAL minimum over all valid billiard orbits.

**Test:** Verify LP solution ≤ all enumerated heuristic solutions.

**3.1.3 Dual polygon construction**

**Statement:** K₂° (polar of K₂) computed correctly from H-rep of K₂.

For K₂ with normals {n_i}, heights {h_i}:
```
K₂° has vertices at {n_i / h_i}
```

**Source:** Standard convex geometry (Schneider 2014)

**Test:** Verify polar vertices match formula.

### 3.2 HK2019 Algorithm (Haim-Kislev 2019)

**Applicability:** All convex polytopes in ℝ⁴.

**Main theorem:**
```
c_EHZ(K) = (1/2) · [max_{σ,β} Q(σ,β)]⁻¹
```

where
```
Q(σ,β) = Σ_{j<i} β_{σ(i)} β_{σ(j)} ω(n_{σ(i)}, n_{σ(j)})
```

**Source:** Haim-Kislev 2019, Theorem 1.1

**3.2.1 Q-value for tesseract**

**Statement:** For tesseract, max Q = 0.125, giving c = 4.0.

**Test:** Compute Q for known optimal σ, verify Q = 0.125.

**3.2.2 Closure constraint**

**Statement:** Optimal β satisfies:
```
Σᵢ βᵢ · nᵢ = 0  (vector equation in ℝ⁴)
```

**Source:** Haim-Kislev 2019, Lemma 3.2 (orbit closure condition)

**Test:** Extract optimal β from HK2019; verify ‖Σ βᵢnᵢ‖ < ε.

**Failure indicates:** QP solver constraint violation.

**3.2.3 Height normalization**

**Statement:** Optimal β satisfies:
```
Σᵢ βᵢ · hᵢ = 1
```

**Source:** Haim-Kislev 2019, normalization convention

**Test:** Extract optimal β; verify |Σ βᵢhᵢ - 1| < ε.

**3.2.4 β non-negativity**

**Statement:** All βᵢ ≥ 0.

**Test:** Verify all components of optimal β are non-negative.

### 3.3 Tube Algorithm (Chaidez-Hutchings 2021)

**Applicability:** Polytopes with non-Lagrangian 2-faces.

**3.3.1 Rotation range**

**Statement:** For each non-Lagrangian 2-face F:
```
ρ(F) ∈ (0, 1/2)
```

**Source:** CH2021, Corollary 5.3

**Test:** Verify all computed rotations are in valid range.

**3.3.2 Total rotation for closed orbit**

**Statement:** For action-minimizing orbit with CZ index 3:
```
ρ_total = Σᵢ ρ(Fᵢ) ∈ (1, 2)
```

**Source:** CH2021, Proposition 1.10

**Test:** Verify closed orbit rotation sum in range.

**WARNING:** Previous code had `rotation == 1.0` check which is UNCITED and likely wrong.

**3.3.3 Transition matrices are symplectic**

**Statement:** Each ψ_F ∈ Sp(2):
```
det(ψ_F) = 1
ψ_Fᵀ J₂ ψ_F = J₂
```

**Source:** Standard symplectic geometry

**Test:** For each transition matrix, verify symplecticity.

### 3.4 Algorithm Agreement

**Statement:** On their common domain (Lagrangian products), Billiard and HK2019 should agree:
```
|c_billiard - c_HK2019| / c_billiard < ε
```

**Source:** Both compute same invariant by different methods.

**Test:** For each Lagrangian product, verify relative error < 1%.

**Failure indicates:** At least one algorithm is wrong.

---

## 4. Geometric Properties

These are foundational math facts used by the algorithms.

### 4.1 Support Function

**Definition:** For convex K ⊂ ℝⁿ:
```
h_K(v) = max_{x∈K} ⟨x, v⟩
```

**Source:** Schneider 2014, Definition 1.7.1

**Properties to test:**

**4.1.1 Positive homogeneity:**
```
h_K(λv) = λ · h_K(v)  for λ ≥ 0
```

**4.1.2 Subadditivity:**
```
h_K(u+v) ≤ h_K(u) + h_K(v)
```

**4.1.3 For H-rep polytope:**
```
h_K(v) = max_j ⟨v, vertex_j⟩
```
where vertices are computed from H-rep.

**Test:** For tesseract, h(e₁) = 1, h(e₁+e₂) = 2.

### 4.2 Polar Body

**Definition:**
```
K° = {y ∈ ℝⁿ : h_K(y) ≤ 1} = {y : ⟨x,y⟩ ≤ 1 ∀x∈K}
```

**Source:** Schneider 2014, Section 1.6

**Properties to test:**

**4.2.1 Double polar:**
```
(K°)° = K  (for origin-symmetric convex bodies)
```

**4.2.2 H-rep to V-rep:**
For K with outward normals {n_i} and heights {h_i}:
```
K° has vertices at {n_i / h_i}
```

**Test:** Tesseract has polar 16-cell (cross-polytope).

### 4.3 Symplectic Form

**Definition:** Standard symplectic form on ℝ⁴ = ℝ²_q × ℝ²_p:
```
ω(x, y) = ⟨Jx, y⟩
```
where J(q,p) = (-p, q).

**Coordinate formula:**
```
ω((q₁,q₂,p₁,p₂), (q₁',q₂',p₁',p₂')) = q₁p₁' + q₂p₂' - p₁q₁' - p₂q₂'
```

**Source:** McDuff-Salamon 2017, Chapter 1

**Properties to test:**

**4.3.1 Antisymmetry:**
```
ω(u, v) = -ω(v, u)
```

**4.3.2 Bilinearity:**
```
ω(au + bv, w) = a·ω(u,w) + b·ω(v,w)
```

**4.3.3 Non-degeneracy:**
```
ω(u, v) = 0 ∀v ⟹ u = 0
```

**4.3.4 Standard basis:**
```
ω(e₁, e₃) = 1   (q₁, p₁ canonical pair)
ω(e₂, e₄) = 1   (q₂, p₂ canonical pair)
ω(e₁, e₂) = 0   (q₁, q₂ Lagrangian)
```

### 4.4 Lagrangian Subspaces and 2-Faces

**Definition:** A subspace L ⊂ ℝ⁴ is Lagrangian if dim(L) = 2 and ω|_L = 0.

**For polytope 2-faces:**
A 2-face F_ij (intersection of facets i and j) is Lagrangian iff:
```
ω(n_i, n_j) = 0
```

**Source:** CH2021, Definition 3.3

**Tests:**

**4.4.1 Tesseract 2-faces:**
The tesseract has 20 Lagrangian and 8 non-Lagrangian 2-faces. Axis-aligned normals give:
```
ω(e₁, e₂) = 0   (Lagrangian, forms a 2-face)
ω(e₃, e₄) = 0   (Lagrangian, forms a 2-face)
ω(e₁, e₃) ≠ 0   (non-Lagrangian, forms a 2-face)
```

**4.4.2 Perturbed tesseract:**
After perturbation, some 2-faces become non-Lagrangian:
```
ω(n_i, n_j) ≠ 0  for some pairs
```

**Test:** Count Lagrangian vs non-Lagrangian 2-faces.

---

## 5. Witness Orbit Properties

The algorithm returns a witness: an actual orbit achieving the capacity. This orbit must satisfy geometric constraints.

### 5.1 Breakpoints on Facets

**Statement:** Each breakpoint p_i lies on its claimed facet F_{k_i}:
```
⟨n_{k_i}, p_i⟩ = h_{k_i}
```

**Source:** Definition of polytope boundary

**Test:** For each breakpoint, verify |⟨n_k, p⟩ - h_k| < ε.

**Tested:** ✓

**Failure indicates:** Incorrect breakpoint computation.

### 5.2 Orbit Closure

**Statement:** The orbit is closed:
```
γ(T) = γ(0)
```
where T = total period.

**Source:** Definition of periodic orbit

**Test:** Verify ‖p_last - p_first‖ < ε.

**Tested:** ✗ (segment_times are placeholder zeros)

**Known issue:** Segment times not properly derived from Reeb flow.

### 5.3 Action Equals Capacity

**Statement:** The symplectic action of the orbit equals the capacity:
```
A(γ) = ∮_γ λ = Σᵢ segment_times[i] = c
```

**Source:** Hofer-Zehnder 1994, Definition of EHZ capacity

**Test:** Verify |Σ segment_times - capacity| < ε.

**Tested:** ✗ (segment_times not implemented)

### 5.4 Reeb Flow Differential Inclusion

**Statement:** On each facet segment, velocity satisfies Reeb flow:
```
γ'(t) ∈ cone of Jn  (for facets touched at time t)
```

More precisely, at a point on facet F_i:
```
γ'(t) = λ · Jn_i  for some λ > 0
```

At corners (intersection of facets F_i ∩ F_j):
```
γ'(t) ∈ cone(Jn_i, Jn_j)
```

**Source:** CH2021, Definition 3.8

**Test:** Verify max_flow_error < ε where:
```
flow_error = min_{λ≥0} ‖γ'(t) - λJn‖
```

**Tested:** Computed but NOT asserted. This is a critical gap.

**Failure indicates:** Orbit is not a valid Reeb orbit (fundamental algorithm bug).

### 5.5 Convexity of Orbit

**Statement:** For convex bodies, the projection of the orbit onto configuration space (q₁, q₂) should be convex.

**Source:** Derived from convexity of K₁ in billiard formulation

**Test:** Verify convexity of projected orbit.

**Tested:** ✗

---

## 6. Algorithm Agreement and Domain Coverage

### 6.1 Billiard = HK2019 on Lagrangian products

**Statement:** For Lagrangian products K₁ × K₂:
```
c_billiard(K₁ × K₂) = c_HK2019(K₁ × K₂)
```

**Source:** Both compute same EHZ capacity by different methods.

**Test:** For random Lagrangian products, verify relative error < 1%.

**Tested:** ✓ (proptest with 3-10 cases)

**Failure indicates:** At least one algorithm has a bug.

### 6.2 Domain Table

| Algorithm | Lagrangian products | General polytopes | Notes |
|-----------|--------------------|--------------------|-------|
| Billiard | ✓ | ✗ | Rudolf 2022 |
| HK2019 | ✓ | ✓ | O(F!) complexity |
| Tube | ✗ (degenerate) | ✓ | CH2021 |

**Test:** Verify each algorithm handles its domain and rejects/fails gracefully outside it.

### 6.3 Tube Fails on Lagrangian Products

**Statement:** For Lagrangian products, tube algorithm fails because they have Lagrangian 2-faces. The tube algorithm requires ALL normal pairs to be non-Lagrangian for valid transition matrices.

**Source:** CH2021, requires ω(n_i, n_j) ≠ 0 for ALL transition matrices.

**Test:** Verify tube fails on tesseract, triangle×triangle, pentagon×pentagon.

**Tested:** ✓ (tesseract only)

### 6.4 HK2019 Timeout on Large Polytopes

**Statement:** HK2019 has O(F!) complexity, becomes impractical for F > 10.

**Test:** Verify timeout or resource limit for 12-facet polytopes.

**Tested:** Implicitly (pentagon×pentagon times out)

---

## 7. Priority Order for Implementation

### HIGH Priority (Fundamental Trust)

1. **Ground truth values** (§2): Fix triangle and pentagon fixtures, add more polytopes
2. **Symplectomorphism invariance** (§1.3): Fundamental axiom, completely untested
3. **Witness flow error assertion** (§5.4): Already computed, just needs assertion
4. **Algorithm agreement expansion** (§6.1): More than 3 proptest cases

### MEDIUM Priority (Deeper Validation)

5. **HK2019 constraint verification** (§3.2): Verify β closure and normalization
6. **Support function properties** (§4.1): Foundation for billiard algorithm
7. **Rotation number properties** (§3.3): Tube algorithm validation
8. **Orbit closure** (§5.2): Requires fixing segment_times

### LOW Priority (Extended Coverage)

9. **n-gon convergence to π** (§1.4): Asymptotic behavior
10. **Cross-polytope and 24-cell** (§2.6, §2.7): Extend beyond tesseract
11. **Duality properties** (polar body capacity)

---

## 8. Capacity-Volume Inequalities

### 8.1 Viterbo's Conjecture (for convex bodies)

For convex K ⊂ ℝ²ⁿ with volume V(K):

c(K)ⁿ / V(K) ≤ c(B)ⁿ / V(B) = πⁿ / V(B²ⁿ)

Equality iff K is an ellipsoid.

**Status:** DISPROVEN by HK-O 2024 pentagon counterexample (systolic ratio > 1).

**Test:** Verify pentagon×pentagon has systolic ratio = 1.047 > 1.

### 8.2 Systolic Ratio

ρ(K) = c(K)² / (2 · Vol(K))  for 4D bodies

For K = B₁ × B₂ (Lagrangian product):
ρ(K) = c(K)² / (2 · Area(B₁) · Area(B₂))

**Test:** Compute for various products, verify ρ ≤ 1 for "nice" polytopes, ρ > 1 for pentagon.

---

## 9. Ellipsoid Formulas

### 9.1 All capacities coincide on ellipsoids

For ellipsoid E with semi-axes a₁ ≤ a₂ ≤ ... ≤ aₙ in ℝ²ⁿ:

c(E) = π · a₁²

where a₁ is the smallest semi-axis.

**Test:** Create 4D ellipsoid, verify capacity = π·(smallest semi-axis)².

### 9.2 Ball capacity

c(B²ⁿ(r)) = π · r²

**Test:** Approximate ball with high-vertex-count polygon products, verify → πr².

---

## 10. Convergence Properties

### 10.1 Regular n-gon → disk

As n → ∞, regular n-gon product should approach disk capacity:

c(Pₙ × Pₙ) → π · r²

where r is the circumradius.

**Test:** Compute for n = 4, 5, 6, 8, 12, verify monotonic increase toward π.

| n | c(Pₙ×Pₙ)/r² | Expected limit |
|---|-------------|----------------|
| 3 | 1.5 | → π ≈ 3.14 |
| 4 | 4.0 | |
| 5 | ? | |
| 6 | ? | |

---

## 11. Duality Properties

### 11.1 Polar body capacity (conjecture)

For centrally symmetric K:

c(K) · c(K°) ≥ 4

with equality for cubes/cross-polytopes?

**Test:** Compute c(tesseract) · c(16-cell), check relationship.

### 11.2 Mahler's inequality connection

Vol(K) · Vol(K°) ≥ 4ⁿ/n! (Mahler)

Is there an analogous capacity inequality?

---

## 12. Product Formulas

### 12.1 Lagrangian product capacity

c(K₁ × K₂) = minimal T-length of (K₁, K₂°)-Minkowski billiard

**Test:** Verified by billiard algorithm; cross-check against HK2019.

### 12.2 Capacity vs product of widths

For rectangle product [−a,a] × [−b,b] × [−a,a] × [−b,b]:

c = 4 · min(a,b)²  (for squares)
c = 4ab  (for rectangles where a ≠ b?)

**Test:** Verify for various rectangle dimensions.

---

## 13. Rotation Number Properties (Tube Algorithm)

### 13.1 Rotation in (0, 1/2)

For each non-Lagrangian 2-face F, rotation ρ(F) ∈ (0, 1/2).

**Test:** For perturbed tesseract, verify all ρ(F) in range.

### 13.2 Rotation additivity

Total rotation over closed orbit: ρ_total = Σᵢ ρ(Fᵢ)

For action-minimizing orbit: ρ_total ∈ (1, 2) per CH2021 Prop 1.10.

**Test:** For any closed orbit found, verify rotation sum in range.

### 13.3 Transition matrices are symplectic

ψ_F ∈ Sp(2) for each 2-face transition.

**Test:** For each ψ_F, verify det(ψ_F) = 1 and ψᵀJψ = J.

---

## 14. Polytopes to Use (NOT just tesseract!)

| Polytope | Facets | Type | Use For |
|----------|--------|------|---------|
| Tesseract | 8 | Lagrangian product | ✓ Currently used |
| Triangle×Triangle | 6 | Lagrangian product | Ground truth 1.5 |
| Pentagon×Pentagon | 10 | Lagrangian product | Counterexample 3.441 |
| Hexagon×Hexagon | 12 | Lagrangian product | Convergence to π |
| Rectangle 2×1 | 8 | Lagrangian product | Scaling tests |
| Simplex ℝ⁴ | 5 | NOT Lagrangian | HK2019 only, c=0.25 |
| 16-cell | 16 | NOT Lagrangian | Dual of tesseract |
| 24-cell | 24 | NOT Lagrangian | Tube algorithm |
| Random polygons | varies | Lagrangian product | Proptests |
| Perturbed tesseract | 8 | NOT Lagrangian | Tube algorithm |

---

## 15. Summary: What We Test vs What We Should Test

### Current Test Coverage

| Category | Property | Tested? | Priority | Notes |
|----------|----------|---------|----------|-------|
| **Axioms** | Scaling c(λK) = λ²c(K) | Partial | HIGH | Only tesseract |
| | Monotonicity K⊆L ⟹ c(K)≤c(L) | Partial | HIGH | Via proptest |
| | Symplectomorphism invariance | ✗ | **CRITICAL** | Completely untested |
| **Ground Truth** | Tesseract = 4.0 | ✓ | - | Only verified value |
| | Triangle×Triangle = 1.5 | ✗ | HIGH | Fixture broken |
| | Pentagon×Pentagon = 3.441 | ✗ | HIGH | Fixture broken |
| | Simplex = 0.25 | ✗ | MEDIUM | Needs citation |
| | Rectangle 2×1 = 1.0 | ✓ | - | Working |
| **Witness** | Breakpoints on facets | ✓ | - | Working |
| | Orbit closure | ✗ | HIGH | segment_times zeros |
| | Action = capacity | ✗ | HIGH | segment_times zeros |
| | Reeb flow error | Computed | **CRITICAL** | Not asserted |
| **Algorithm** | Billiard-HK2019 agreement | ✓ | - | 3-10 proptest cases |
| | HK2019 β constraints | ✗ | MEDIUM | Closure/normalization |
| | Tube rotation range | ✗ | MEDIUM | |
| **Misc** | Systolic ratio | ✗ | MEDIUM | Depends on pentagon |
| | n-gon → π convergence | ✗ | LOW | |

### Critical Gaps

1. **Symplectomorphism invariance is COMPLETELY UNTESTED.** This is a fundamental capacity axiom.

2. **Only ONE ground truth value (tesseract) is verified.** Triangle and pentagon fixtures are broken.

3. **Witness Reeb flow error is computed but NOT asserted.** The orbit might not be a valid Reeb orbit.

4. **Tests do not sample full argument classes:**
   - Sp(4) invariance: Only (q₁,p₁) rotation tested (1D of 10D group)
   - Polytopes: Only tesseract and random polygons tested
   - Scaling: Only λ=2 tested

### What Would Catch Common Bugs

| Bug Type | Catching Test |
|----------|---------------|
| Wrong capacity formula | Ground truth tests (§2) |
| Wrong J matrix | Symplectic form tests (§4.3) |
| Wrong polar computation | Polar body tests (§4.2) |
| Missing orbit candidates | Bounce count test (§3.1.1) |
| Invalid witness | Reeb flow assertion (§5.4) |
| QP solver failure | β constraint tests (§3.2) |
| Rotation formula error | Rotation range tests (§3.3) |

---

## 16. References

### Primary Sources

- **Ekeland-Hofer 1989:** "Symplectic topology and Hamiltonian dynamics"
- **Gromov 1985:** "Pseudo holomorphic curves in symplectic manifolds"
- **Hofer-Zehnder 1994:** "Symplectic Invariants and Hamiltonian Dynamics"
- **Haim-Kislev 2019:** "On the Symplectic Size of Convex Polytopes" (HK2019 algorithm)
- **Rudolf 2022:** "The Minkowski Billiard Characterization of the EHZ-Capacity" (Billiard algorithm)
- **Chaidez-Hutchings 2021:** "Computing Reeb Dynamics on Polytopes" (Tube algorithm)
- **Haim-Kislev & Ostrover 2024:** "A Counterexample to Viterbo's Conjecture" (Pentagon counterexample)

### Textbooks

- **Schneider 2014:** "Convex Bodies: The Brunn-Minkowski Theory"
- **McDuff-Salamon 2017:** "Introduction to Symplectic Topology"

### Internal Documentation

- `archive/billiard-correctness-proof.md`: Mathematical derivations for billiard algorithm
- `algorithm-hk2019-spec.md`: HK2019 algorithm specification
- `test-cases.md`: Test case catalog with expected values
