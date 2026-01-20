# Mathematical Claims Reference

**Purpose:** Single source of truth for all mathematical claims used in the Rust codebase.

Every claim has:
- Statement (the mathematical fact)
- Citation (paper + theorem/equation, or `[UNCITED]` if needs verification)
- Verification status (tested, untested, or known issues)
- Code location (where the claim is used)

---

## 1. Capacity Axioms

### 1.1 Scaling: c(lambda K) = lambda^2 c(K)

**Statement:** For any convex body K in R^4 and lambda > 0:
```
c(lambda K) = lambda^2 * c(K)
```

**Citation:** Ekeland-Hofer 1989, Axiom (iii); Hofer-Zehnder 1994, Theorem 3.

**Why quadratic:** Action = integral of p dq has units of [length]^2, hence scales as lambda^2.

**Verification:** Tested for tesseract with lambda=2 (capacity_scaling_axiom.rs). Other polytopes: partial.

**Code location:** Used implicitly in all capacity computations; tested in `tests/capacity_scaling_axiom.rs`.

---

### 1.2 Monotonicity: K subset L implies c(K) <= c(L)

**Statement:** If K is a subset of L (as sets), then c(K) <= c(L).

**Citation:** Ekeland-Hofer 1989, Axiom (ii); follows from infimum definition.

**Verification:** Tested via proptest for random Lagrangian products (capacity_monotonicity.rs).

**Code location:** `tests/capacity_monotonicity.rs`.

---

### 1.3 Symplectomorphism Invariance: c(AK) = c(K) for A in Sp(4)

**Statement:** For any A in Sp(4,R) and convex K:
```
c(AK) = c(K)
```

**Citation:** Ekeland-Hofer 1989, Axiom (i); Gromov 1985 non-squeezing.

**Verification:** Partial tests for block rotations (capacity_symplectomorphism.rs). Full Sp(4) coverage is incomplete.

**Code location:** `tests/capacity_symplectomorphism.rs`.

---

### 1.4 Conformality: c(B^4) = pi

**Statement:**
```
c(B^4(1)) = pi      (unit 4-ball)
c(Z^4(1)) = pi      (cylinder B^2(1) x R^2)
```

**Citation:** Gromov 1985; Hofer-Zehnder 1994, Theorem 1.

**Note:** These are smooth bodies, not polytopes. For regular n-gon products, capacity converges to pi as n increases.

**Verification:** Not tested (polytope approximation would be needed).

---

## 2. Known Capacity Values

### 2.1 Tesseract: c([-1,1]^4) = 4.0

**Statement:**
```
c_EHZ([-1,1]^4) = 4.0
```

**Citation:** Haim-Kislev 2019, Example 4.6; Rudolf 2022, Example 3.5.

**Derivation:** For square x square where square = [-1,1]^2, optimal orbit bounces along x_1=+-1, x_3=+-1 faces with period 4.

**Verification:** Tested via billiard and HK2019 algorithms (capacity_known_values.rs). All algorithms agree.

**Code location:** `tests/capacity_known_values.rs`.

---

### 2.2 Equilateral Triangle x Triangle: c = 1.5 r^2

**Statement:** For equilateral triangle T with circumradius r:
```
c_EHZ(T x T) = 1.5 * r^2
```

For r=1: c = 1.5

**Citation:** [UNCITED - NEEDS LITERATURE VERIFICATION]. Verified computationally via LP and HK2019 agreement.

**Critical Note:** The Fagnano orbit (edge midpoints, t=0.5) gives T-length 2.25, but this is NOT optimal for Minkowski billiards. The optimal orbit hits edges at t=1/3, giving T-length 1.5.

**Verification:** Billiard (LP) and HK2019 algorithms agree on 1.5.

**Code location:** `archive/billiard-correctness-proof.md` Section 7, 9; `tests/capacity_known_values.rs`.

---

### 2.3 Pentagon x Rotated Pentagon (HK-O Counterexample): c approx 3.441

**Statement:** For regular pentagon K with circumradius 1, and T = K rotated by 90 degrees:
```
c_EHZ(K x T) = 2*cos(pi/10)*(1 + cos(pi/5)) = 3.4409548011...
```

Exact formula involving golden ratio phi:
```
c = (sqrt(5) + 1)/2 * (1 + (sqrt(5) + 1)/4) = phi * (1 + phi/2)
```

**Citation:** Haim-Kislev & Ostrover 2024, "A Counterexample to Viterbo's Conjecture", Proposition 1.

**Significance:** This is a COUNTEREXAMPLE to Viterbo's conjecture. Systolic ratio exceeds 1:
```
rho = c^2 / (2*Vol) = (sqrt(5) + 3) / 5 = 1.0472...
```

**Verification:** [KNOWN BUG] Billiard algorithm returns 2.127, which is expected/phi. Investigation ongoing (see next-actions.md).

**Code location:** Test is `#[ignore]` in `tests/capacity_known_values.rs`.

---

### 2.4 Standard Simplex in R^4: c = 1/(2n) = 0.25

**Statement:** For the standard 4-simplex Delta^4 = conv{0, e_1, e_2, e_3, e_4}:
```
c_EHZ(standard simplex in R^{2n}) = 1/(2n)
```

For n=2: c = 0.25.

**Citation:** [UNCITED - NEEDS VERIFICATION]. Claimed in Haim-Kislev thesis (2019), but exact reference (theorem number, page) not confirmed.

**Note:** The simplex is NOT a Lagrangian product, so billiard algorithm cannot be used. Only HK2019 applies.

**Verification:** Not tested.

---

### 2.5 Rectangle Products

**Statement:** For rectangle R(a,b) = [-a,a] x [-b,b] with a >= b:
```
c_EHZ(R(a,b) x R(a,b)) = 4*min(a,b)^2 = 4b^2
```

**Citation:** Direct computation; special case of tesseract when a=b=1.

**Verification:** Tested for 1x1 (tesseract) and 1x0.5. Other dimensions not tested.

**Code location:** `tests/capacity_known_values.rs`.

---

## 3. Algorithm-Specific Claims

### 3.1 Billiard Algorithm (Rudolf 2022)

#### 3.1.1 Main Characterization

**Statement:** For K polytope and T strictly convex, action-minimizing closed characteristics on boundary(K x T) correspond to closed (K,T)-Minkowski billiard trajectories in K with dual trajectories in T.

**Citation:** Rudolf 2022, Theorem 3. arXiv:2203.01718

**Code location:** `billiard.rs` module docstring.

---

#### 3.1.2 Bounce Count Bound

**Statement:** The T-minimizing closed (K,T)-Minkowski billiard trajectory has at most n+1 bouncing points where n = dim(K). For n=2 (planar polygons): at most 3 bounces.

**Citation:** Rudolf 2022, Theorem 4. arXiv:2203.01718

**Verification:** Algorithm considers 2-bounce and 3-bounce trajectories.

**Code location:** `billiard_lp.rs`.

---

#### 3.1.3 T-length Formula

**Statement:** The T-length of a trajectory with vertices q_1,...,q_m is:
```
l_T(q_1,...,q_m) = sum_j h_T(q_{j+1} - q_j)
```
where h_T is the support function of T.

**Citation:** Rudolf 2022, Section 2.

**Code location:** `billiard_lp.rs` (LP objective function).

---

#### 3.1.4 Support Function Properties

**Statement:**
- Positive homogeneity: h_K(lambda v) = lambda * h_K(v) for lambda >= 0
- Subadditivity: h_K(u+v) <= h_K(u) + h_K(v)
- For polytope K with vertices {v_j}: h_K(d) = max_j <d, v_j>

**Citation:** Schneider 2014, "Convex Bodies: The Brunn-Minkowski Theory", Definition 1.7.1.

**Verification:** Tested in `tests/polygon_2d.rs`.

**Code location:** `billiard.rs::Polygon2DSimple::support`.

---

### 3.2 HK2019 Algorithm (Haim-Kislev 2017)

#### 3.2.1 Main Capacity Formula

**Statement:**
```
c_EHZ(K) = (1/2) * [max_{sigma, beta} Q(sigma, beta)]^{-1}
```
where:
- Q(sigma, beta) = sum_{j<i} beta_{sigma(i)} * beta_{sigma(j)} * omega(n_{sigma(i)}, n_{sigma(j)})
- M(K) = {beta_i >= 0, sum beta_i h_i = 1, sum beta_i n_i = 0}

**Citation:** HK2017 Theorem 1 (arXiv:1712.03494).

**Verification:** [INCOMPLETE] Current QP solver only checks 0D and 1D faces. Tests pass by luck.

**Code location:** `hk2019.rs::compute_hk2019_capacity`.

---

#### 3.2.2 Q is Indefinite

**Statement:** The quadratic form Q(sigma, beta) is INDEFINITE (the symplectic form has mixed signs), so the maximum may be at vertices, edges, or higher-dimensional face interiors.

**Citation:** Standard linear algebra + symplectic form definition.

**Verification:** This is why vertex enumeration is incomplete.

**Code location:** `hk2019.rs` module warning.

---

#### 3.2.3 [KNOWN INCORRECT] "CH2021 Theorem 1.4 rotation bound"

**Statement:** Previous documentation claimed "CH2021 Theorem 1.4: rotation bound restricts valid permutations" but no such theorem exists in CH2021.

**Citation:** [KNOWN INCORRECT - NO SUCH THEOREM]

**Status:** This false claim has been removed from code, but may appear in old session handoffs.

---

### 3.3 Tube Algorithm (Chaidez-Hutchings 2021)

#### 3.3.1 Rotation Range per 2-Face

**Statement:** For each non-Lagrangian 2-face F:
```
rho(F) in (0, 1/2)
```

**Citation:** CH2021, Corollary 5.3.

**Verification:** Tested in `tube.rs` unit tests.

**Code location:** `tube.rs`, `polytope.rs::TwoFaceData::rotation`.

---

#### 3.3.2 Total Rotation for Action-Minimizing Orbit

**Statement:** For action-minimizing orbit with CZ index 3:
```
rho_total = sum_i rho(F_i) in (1, 2)
```

**Citation:** CH2021, Proposition 1.10.

**Verification:** [INCOMPLETE] No end-to-end test with known capacity result.

**Code location:** `compute.rs`.

---

#### 3.3.3 Periodic Orbit = Fixed Point of Flow Map

**Statement:** A periodic orbit corresponds to a cycle in the flow graph where the flow map phi_p has a fixed point.

**Citation:** CH2021, Definition 3.12.

**Critical Note:** Previous code had `rotation == 1.0` check that was INCORRECT. Closure requires a fixed point, NOT rotation = 1.0.

**Code location:** `compute.rs::solve_closed_tube`.

---

#### 3.3.4 Transition Matrices are Symplectic

**Statement:** Each transition matrix psi_F is in Sp(2):
```
det(psi_F) = 1
psi_F^T J_2 psi_F = J_2
```

**Citation:** Standard symplectic geometry; follows from convexity of K and quaternion structure.

**Verification:** Tested in `geom/symplectic.rs`.

**Code location:** `tube.rs::transition_matrix`.

---

#### 3.3.5 Flow Map is Affine

**Statement:** The flow map phi: F_{i,k} -> F_{k,j} along facet E_k is affine:
```
phi(p) = p + t(p) * v_k
```
where t(p) is the time to reach the next 2-face (affine in p).

**Citation:** CH2021 Section 2; also tube-geometry-spec.md Section 3.

**Verification:** Tested in `tube.rs` unit tests.

**Code location:** `tube.rs::compute_flow_map`.

---

#### 3.3.6 Time to Next 2-Face Formula

**Statement:**
```
t(p) = h_k (h_j - <n_j, p>) / (2 * omega(n_k, n_j))
```

**Citation:** tube-geometry-spec.md Section 3.2 (derived from basic Reeb dynamics).

**Verification:** Tested in `tube.rs` unit tests.

**Code location:** `tube.rs::compute_flow_map`.

---

## 4. Geometric Foundations

### 4.1 Symplectic Form

**Statement:** Standard symplectic form on R^4 = R^2_q x R^2_p:
```
omega(x, y) = <Jx, y>
```
where J(q,p) = (-p, q).

Coordinate formula:
```
omega((q_1,q_2,p_1,p_2), (q_1',q_2',p_1',p_2')) = q_1 p_1' + q_2 p_2' - p_1 q_1' - p_2 q_2'
```

**Citation:** McDuff-Salamon 2017, "Introduction to Symplectic Topology", Chapter 1.

**Verification:** Tested in `geom/symplectic.rs`: antisymmetry, bilinearity, standard basis values.

**Code location:** `geom/symplectic.rs::symplectic_form`.

---

### 4.2 Lagrangian 2-Faces

**Statement:** A 2-face F_{ij} (intersection of facets i and j) is Lagrangian iff:
```
omega(n_i, n_j) = 0
```

**Citation:** CH2021, Definition 3.3.

**Verification:** Tested for tesseract (all 2-faces Lagrangian).

**Code location:** `polytope.rs::PolytopeData`.

---

### 4.3 Flow Direction at 2-Faces

**Statement:** For non-Lagrangian 2-face F_{ij}:
- If omega(n_i, n_j) > 0: flow crosses from E_i into E_j
- If omega(n_i, n_j) < 0: flow crosses from E_j into E_i

**Citation:** tube-geometry-spec.md Section 2.3; follows from Reeb velocity formula.

**Verification:** Tested in `tube.rs` unit tests.

**Code location:** `polytope.rs::FlowDir`, `tube.rs`.

---

### 4.4 Reeb Velocity on Facet

**Statement:** On facet E_i, the Reeb velocity is:
```
v_i = (2/h_i) * J n_i
```

**Citation:** tube-geometry-spec.md Section 2.1; standard Reeb dynamics on convex polytopes.

**Verification:** [UNCITED - NEEDS VERIFICATION] The factor of 2 and normalization need citation.

**Code location:** `tube.rs` (implicit in flow computations).

---

### 4.5 Polar Body

**Statement:** For K with outward normals {n_i} and heights {h_i}:
```
K^o has vertices at {n_i / h_i}
```

Double polar: (K^o)^o = K (for origin-symmetric convex bodies).

**Citation:** Schneider 2014, Section 1.6.

**Verification:** Tested in `tests/polygon_2d.rs`.

**Code location:** `billiard.rs::Polygon2DSimple::polar`.

---

### 4.6 Quaternion Structure

**Statement:** Quaternion matrices i, j, k in O(4) satisfying:
```
i^2 = j^2 = k^2 = -I
ij = k, jk = i, ki = j
i = J (our almost complex structure)
```

**Citation:** Standard quaternion algebra; verified against thesis conventions.

**Verification:** Tested in `geom/quaternion.rs` (9 tests for quaternion relations).

**Code location:** `geom/quaternion.rs`.

---

### 4.7 Trivialization of 2-Face Tangent Space

**Statement:** For non-Lagrangian 2-face F with flow entering facet E_j:
```
tau_F(V) = (<V, j n_j>, <V, k n_j>)
```
This is a symplectic isomorphism (TF, omega|_TF) -> (R^2, omega_0).

**Citation:** tube-geometry-spec.md Section 4.2; CH2021.

**Verification:** Tested in `geom/symplectic.rs`.

**Code location:** `geom/symplectic.rs::trivialization`.

---

## 5. Witness Orbit Properties

### 5.1 Breakpoints on Facets

**Statement:** Each breakpoint p_i lies on its claimed facet F_{k_i}:
```
<n_{k_i}, p_i> = h_{k_i}
```

**Citation:** Definition of polytope boundary.

**Verification:** Tested in `tests/billiard_witness.rs`.

---

### 5.2 Reeb Flow Differential Inclusion

**Statement:** On each facet segment, velocity satisfies:
```
gamma'(t) = lambda * J n_i  for some lambda > 0
```

At corners (intersection F_i intersect F_j):
```
gamma'(t) in cone(J n_i, J n_j)
```

**Citation:** CH2021, Definition 3.8.

**Verification:** [INCOMPLETE] Computed but not asserted. max_flow_error approx 2.36 indicates issues.

**Code location:** `result.rs::verify_differential_inclusion`.

---

### 5.3 Action Equals Period

**Statement:** For Reeb dynamics, the action equals the period:
```
A(gamma) = integral_gamma lambda = sum_i segment_times[i] = T
```

**Citation:** Hofer-Zehnder 1994, Definition of EHZ capacity.

**Verification:** [INCOMPLETE] segment_times not implemented (placeholder zeros).

---

## 6. Viterbo's Conjecture

### 6.1 Statement (Disproven)

**Statement:** For convex K in R^{2n}:
```
c(K)^n / V(K) <= c(B)^n / V(B) = pi^n / V(B^{2n})
```
Equality iff K is an ellipsoid.

**Citation:** Viterbo 2000 (conjecture); Haim-Kislev & Ostrover 2024 (counterexample).

**Status:** DISPROVEN by pentagon counterexample.

---

### 6.2 Systolic Ratio

**Statement:**
```
rho(K) = c(K)^2 / (2 * Vol(K))  for 4D bodies
```

For HK-O pentagon counterexample: rho = 1.047 > 1.

**Citation:** Haim-Kislev & Ostrover 2024.

**Verification:** Test is `#[ignore]` due to pentagon capacity bug.

---

## 7. Uncited Claims Needing Verification

These claims appear in the codebase without proper citations:

1. **Reeb velocity factor of 2**: The formula v_i = (2/h_i) J n_i needs a citation for the factor of 2.

2. **Triangle capacity 1.5**: No closed-form publication found; verified only computationally.

3. **Simplex capacity 1/(2n)**: Exact theorem/page in Haim-Kislev thesis needs verification.

4. **Tesseract capacity 4.0**: Claimed to be in HK2019 Example 4.6 and Rudolf 2022 Example 3.5 - needs direct verification.

---

## References

### Primary Sources

- **Ekeland-Hofer 1989:** "Symplectic topology and Hamiltonian dynamics"
- **Gromov 1985:** "Pseudo holomorphic curves in symplectic manifolds"
- **Hofer-Zehnder 1994:** "Symplectic Invariants and Hamiltonian Dynamics"
- **Haim-Kislev 2017 (HK2017):** arXiv:1712.03494 "On the Symplectic Size of Convex Polytopes"
- **Rudolf 2022:** arXiv:2203.01718 "The Minkowski Billiard Characterization of the EHZ-Capacity"
- **Chaidez-Hutchings 2021 (CH2021):** "Computing Reeb Dynamics on Polytopes"
- **Haim-Kislev & Ostrover 2024:** arXiv:2405.16513 "A Counterexample to Viterbo's Conjecture"

### Textbooks

- **Schneider 2014:** "Convex Bodies: The Brunn-Minkowski Theory"
- **McDuff-Salamon 2017:** "Introduction to Symplectic Topology"

---

## Document Maintenance

When adding new mathematical claims to the codebase:
1. Add the claim to this document with proper citation
2. Mark verification status
3. Reference code location
4. If uncited, mark as `[UNCITED - NEEDS VERIFICATION]`
