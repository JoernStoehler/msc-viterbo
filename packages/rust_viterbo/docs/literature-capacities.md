# Literature Capacities: Ground Truth Values

**Purpose:** Definitive reference for EHZ capacity and volume values from published literature.
These values are independent of our implementations and serve as test oracles.

**Last updated:** 2026-01-20

**Literature search conducted:** 2026-01-20 (comprehensive search of arXiv, Symplectic Capacities Project, author websites)

---

## Priority 1: Essential Reference Values

### Unit Ball B^4 (Reference/Normalization)

- **Capacity:** pi = 3.14159265...
- **Volume:** (pi^2 / 2) = 4.9348...
- **Source:** Gromov 1985 (non-squeezing theorem); Hofer-Zehnder 1994, Theorem 1
- **Exact formula:** c(B^{2n}(r)) = pi * r^2 (for unit ball, r=1)
- **Notes:** This is the normalization axiom for symplectic capacities. All normalized capacities satisfy c(B^4) = c(Z^4) = pi where Z^4 = B^2 x R^2 is the cylinder.

---

### Tesseract/Hypercube [-1,1]^4

- **Capacity:** 4.0
- **Volume:** 16.0 (since Vol([-1,1]^4) = 2^4 = 16)
- **Source:** Haim-Kislev 2019, Example 4.6; Rudolf 2022, Example 3.5
- **Exact formula:** c([-a,a]^4) = 4a^2 (for a=1, c=4)
- **Notes:** As a Lagrangian product [-1,1]^2 x [-1,1]^2, the optimal billiard trajectory bounces between opposite faces. The action is 4 (perimeter of the square factor in normalized form).
- **Systolic ratio:** rho = c^2 / (2*Vol) = 16 / 32 = 0.5
- **Verification:** MATLAB implementation in Haim-Kislev's GitHub confirms this value.

---

### Pentagon x Rotated Pentagon (HK-O 2024 Counterexample)

- **Capacity:** 2*cos(pi/10)*(1 + cos(pi/5)) = 3.4409548011...
- **Volume:** K has area A_K = (5/2)*sin(2*pi/5) = 2.37764..., so Vol(K x T) = A_K^2 = 5.653...
- **Source:** Haim-Kislev & Ostrover 2024, "A Counterexample to Viterbo's Conjecture", Proposition 1.4, arXiv:2405.16513 (to appear in Annals of Mathematics)
- **Exact formula:** c_EHZ(K x T) = 2*cos(pi/10)*(1 + cos(pi/5))
- **Alternative formula:** Using golden ratio phi = (1+sqrt(5))/2: c = phi * (1 + phi/2) = phi + phi^2/2
- **Systolic ratio:** rho = (sqrt(5) + 3)/5 = 1.0472135955... > 1
- **Notes:** This is the COUNTEREXAMPLE to Viterbo's conjecture. K = regular pentagon inscribed in unit circle, T = K rotated by 90 degrees (NOT by pi/10). The ratio Sys(K x T) > 1 violates Viterbo's prediction.
- **Higher dimensions:** For dimension 2n, systolic ratio = ((sqrt(5)+3)/5)^floor(n/2) using symplectic 2-products.

---

### Standard Simplex in R^{2n}

- **Capacity:** 1/(2n) for standard simplex Delta^{2n} = conv{0, e_1, ..., e_{2n}}
- **For n=1 (R^2):** c = 1/2 = 0.5
- **For n=2 (R^4):** c = 1/4 = 0.25
- **For n=3 (R^6):** c = 1/6 = 0.1667
- **For n=4 (R^8):** c = 1/8 = 0.125
- **Volume:** 1/(2n)! for standard simplex (for n=2: 1/24 = 0.0417)
- **Source:** Nir 2013, "On Closed Characteristics and Billiards in Convex Bodies", Master's Thesis, Tel Aviv University [N]
- **Exact formula:** c_EHZ(Delta^{2n}) = 1/(2n)
- **Notes:** The simplex is NOT a Lagrangian product. Computing its capacity is NP-hard (Leipold-Vallentin 2024). The value 1/(2n) is for the STANDARD simplex with vertices at origin and unit vectors.
- **Systolic ratio bound:** sys(S) <= (2n)! / (n! * (2n)^n) for any simplex S in R^{2n} (Theorem 1.1 of arXiv:2509.19083)

#### Computational Verification (Symplectic Capacities Project)

| Dimension (n) | Computed | Theoretical 1/(2n) |
|---------------|----------|--------------------|
| 1 | 0.5008 | 0.5 |
| 2 | 0.2520 | 0.25 |
| 3 | 0.1700 | 0.1667 |
| 4 | 0.1264 | 0.125 |
| 5 | 0.1021 | 0.1 |

---

### Equilateral Triangle x Triangle (circumradius 1)

- **Capacity:** 1.5 (DERIVED - from algorithm agreement)
- **Volume:** Triangle area = (3*sqrt(3))/4 * r^2 = 1.299... for r=1. Vol(T x T) = 1.6875
- **Source:** Rudolf 2022 proves Viterbo holds for triangle x any convex body, but exact value not stated
- **Exact formula:** c(T x T) = 1.5 * r^2 for circumradius r (computational)
- **Notes:** The Fagnano orbit (edge midpoints) gives T-length 2.25, but the optimal Minkowski trajectory gives T-length 1.5. Viterbo's conjecture holds for triangles (Rudolf 2022, arXiv:2203.02294).
- **Systolic ratio:** Satisfies Sys <= 1 (Viterbo holds)

---

## Priority 2: Additional Reference Values

### Cube x Cross-polytope (MATLAB test case)

- **Definition:** Q = [-1,1]^2 (square), CP = conv{+-e_1, +-e_2} (2D cross-polytope/diamond)
- **Capacity:** Computable via Haim-Kislev MATLAB implementation
- **Source:** Haim-Kislev GitHub, README example: `QXCP = KtimesT(Q, CP); c = EHZ_perms(QXCP)`
- **Notes:** This is a test case in the MATLAB implementation. The Lagrangian product Q x CP in R^4 can be computed exactly.

---

### Cross-polytope / 16-cell in R^4

- **Definition:** conv{+-e_1, +-e_2, +-e_3, +-e_4} in R^4
- **Capacity:** NOT FOUND in closed form
- **Volume:** For conv{+-e_1, ..., +-e_n} in R^{2n}: Vol = 2^{2n}/(2n)! (for n=2: 2/3)
- **Source:** No explicit EHZ capacity found in literature
- **Bound (arXiv:2509.19083):** For rotations R of the cross-polytope: c_EHZ(R*O) <= sqrt(3), so sys(R*O) <= 9/4
- **Notes:** The 4D cross-polytope (16-cell) is the dual of the tesseract. It is NOT a Lagrangian product in the standard embedding. Can be computed via Haim-Kislev's combinatorial formula.

---

### 24-cell (Icositetrachoron)

- **Capacity:** NOT FOUND in published literature
- **Volume:** 8 (for circumradius 1)
- **Source:** No symplectic capacity results found for 24-cell
- **Notes:** The 24-cell is a unique 4D regular polytope with exceptional F_4 symmetry. It has 24 octahedral cells and is self-dual. No EHZ capacity computations were found in the literature. It is NOT a Lagrangian product.

---

### Rectangle Products (aspect ratio a:b)

- **Capacity:** 4*min(a,b)^2 for R(a) x R(b) = [-a,a]^2 x [-b,b]^2
- **Source:** Direct consequence of billiard dynamics; Rudolf 2022, Haim-Kislev 2019
- **Exact formula:** For rectangle [-a,a] x [-b,b] with a >= b, the minimum-length orbit bounces along the shorter dimension
- **Notes:** This is a generalization of the tesseract case. For a=b=1, recovers c=4. Viterbo holds for parallelograms x any convex body.

#### Specific verified cases:
| Dimensions (half-widths) | Capacity |
|--------------------------|----------|
| 1 x 1 | 4.0 |
| 1 x 0.5 | 1.0 |
| 2 x 1 | 4.0 |

---

### Regular n-gon Products (circumradius 1)

From the Symplectic Capacities Project computational results:

| n (edges) | c_EHZ (approximate) | Notes |
|-----------|---------------------|-------|
| 3 (triangle) | ~1.5 | See triangle section |
| 5 (pentagon, rotated 90deg) | 3.4410 | Counterexample |
| 21 | 3.0974 | Approaching pi |
| 30 | 3.1212 | |
| 40 | 3.1314 | |
| infinity (disk) | pi = 3.1416... | Limit |

- **Source:** Symplectic Capacities Project (kylersiegel.xyz/EHZ/)
- **Notes:** These are COMPUTATIONAL results, not closed-form. Regular n-gons inscribed in unit circle approach the disk capacity of pi as n increases.

#### Triangle x Square (Lagrangian product)

From computational results:
| Subintervals (m) | Computed capacity | Notes |
|------------------|-------------------|-------|
| 30 | 3.1651 | Approaching pi |
| 120 | 3.1539 | |

---

### Trapezoid x Convex Body

- **Capacity:** No closed form, but Viterbo conjecture holds
- **Source:** Rudolf 2022 (arXiv:2203.02294)
- **Notes:** Rudolf extended the Viterbo conjecture proof from triangles and parallelograms to trapezoids. The capacity can be computed via Minkowski billiards.

---

## Polydisks and Ellipsoids

### Polydisk P(a,b) = D(a) x D(b)

- **Capacity:** pi * min(a, b)^2 where D(r) is disk of radius r
- **Source:** Ekeland-Hofer 1989; standard result
- **Formula:** c(P(a,b)) = pi * min(a, b)^2
- **Notes:** Polydisks are smooth, not polytopes. For embedding questions, P(1,2) embeds in B^4(a) iff a >= 3 (Hind 2013).

### Ellipsoid E(a_1, ..., a_n) in R^{2n}

- **Capacity:** pi * min{a_i}^2 where a_i are the semi-axes
- **Source:** McDuff-Salamon 2017; Ekeland-Hofer 1989
- **Formula:** c(E) = pi * min{a_i^2}
- **Notes:** For ellipsoids, all symplectic capacities agree.

### 2D Domains (Smooth Boundary)

- **Capacity:** = Lebesgue measure (area)
- **Source:** Siburg (referenced in Symplectic Capacities Project)
- **Notes:** For any compact connected domain with smooth boundary in R^2, symplectic capacity equals area.

---

## Lagrangian Products: General Theory

### Definition

A Lagrangian product K x T in R^{2n} consists of K in the position space (q-coordinates) and T in the momentum space (p-coordinates).

### Key Result (Rudolf 2022)

For convex K and T in R^n:
```
c_EHZ(K x T) = minimal T-length of closed (K,T)-Minkowski billiard in K
```

where T-length = sum of support function h_T evaluated on velocity directions.

- **Source:** Rudolf 2022, Theorem 3 (arXiv:2203.01718)
- **Notes:** Artstein-Avidan & Ostrover first proved this for smooth strictly convex bodies; Rudolf extended to all convex bodies without smoothness or strict convexity assumptions.

### Viterbo's Conjecture Status

Viterbo's conjecture (2000) stated that the ball maximizes capacity among convex bodies of equal volume:
```
c(K)^n / Vol(K) <= c(B)^n / Vol(B)
```

**STATUS: DISPROVEN** by Haim-Kislev & Ostrover 2024 using the pentagon counterexample above.

The conjecture holds for:
- Triangles x any convex body (Rudolf 2022)
- Parallelograms x any convex body (Rudolf 2022)
- Trapezoids x any convex body (Rudolf 2022)

---

## Systolic Ratio Bounds

### Definition

The systolic ratio is:
```
Sys(K) = c_EHZ(K)^n / (n! * Vol(K))
```

For the unit ball B^{2n}, Sys(B) = 1.

### Bounds (arXiv:2509.19083)

For simplices in R^4: sys(S) <= 3/4
For any simplex in R^{2n}: sys(S) <= (2n)! / (n! * (2n)^n)

For 6-vertex polytope K in R^4 with Vol(K) = 1:
- c_EHZ(K) <= sqrt(3)
- sys(K) <= 3/2

### Counterexamples

Pentagon x rotated pentagon achieves sys = 1.0472... > 1, disproving Viterbo.

---

## Computational Complexity

- **EHZ capacity is NP-hard** to compute for polytopes (Leipold-Vallentin 2024, arXiv:2402.09914)
- Reduction from feedback arc set problem in bipartite tournaments to computing EHZ capacity of simplices
- **Source:** Leipold & Vallentin 2024, Proceedings of AMS Series B

---

## Summary Table

| Polytope | c_EHZ | Vol | Systolic Ratio | Status |
|----------|-------|-----|----------------|--------|
| B^4 (unit ball) | pi = 3.1416 | pi^2/2 = 4.93 | 1.0 | Reference |
| [-1,1]^4 (tesseract) | 4.0 | 16 | 0.5 | Verified |
| Pentagon x Pentagon (90deg) | 3.4410 | 5.65 | 1.047 | Counterexample |
| Triangle x Triangle (r=1) | 1.5 | 1.69 | 0.67 | Computational |
| Standard 4-simplex | 0.25 | 1/24 | ~0.75 | Proven (Nir 2013) |
| Cross-polytope (16-cell) | ? | 2/3 | <= 9/4 | Bound only |
| 24-cell | ? | 8 | ? | Not found |
| n-gon x n-gon (r=1, large n) | ~pi | varies | ~1 | Computational |

---

## Computational Resources

### Haim-Kislev MATLAB Implementation
- **Repository:** https://github.com/pazithaimkislev/EHZ-capacity
- **Based on:** GAFA 2019 combinatorial formula
- **Input:** Polytope K as m x 2n matrix (rows = vertices)
- **Output:** c_EHZ(K)
- **Notes:** Slow for many faces, but exact. Test case: cube x cross-polytope.

### Symplectic Capacities Project
- **URL:** https://kylersiegel.xyz/EHZ/
- **Content:** Computed values for regular polygons, simplices, disk approximations
- **Notes:** Numerical approximations, not closed-form values.

### Chaidez-Hutchings Computational Methods
- **Paper:** "Computing Reeb dynamics on 4d convex polytopes" J. Comp. Dyn. 8(4):403-445 (2021)
- **Method:** Combinatorial Reeb flow correspondence to smoothed polytopes
- **Applications:** Testing Viterbo's conjecture, finding systolic ratio 1 examples

---

## References

### Primary Sources for Capacity Values

1. **Gromov 1985:** "Pseudo holomorphic curves in symplectic manifolds" - ball normalization
2. **Ekeland-Hofer 1989:** "Symplectic topology and Hamiltonian dynamics" - capacity axioms
3. **Nir 2013:** "On Closed Characteristics and Billiards in Convex Bodies" Master's Thesis, Tel Aviv University - simplex formula c = 1/(2n)
4. **Haim-Kislev 2019:** "On the Symplectic Size of Convex Polytopes" GAFA 29(2):440-463 - combinatorial formula, tesseract example
5. **Rudolf 2022:** "The Minkowski Billiard Characterization..." J.Dyn.Diff.Equ. 36:2773-2791 (arXiv:2203.01718) - billiard connection
6. **Rudolf 2022:** "Viterbo's conjecture for Lagrangian products in R^4..." (arXiv:2203.02294) - triangle, parallelogram, trapezoid
7. **Haim-Kislev & Ostrover 2024:** "A Counterexample to Viterbo's Conjecture" arXiv:2405.16513 (to appear Annals of Math) - pentagon counterexample
8. **Leipold & Vallentin 2024:** "Computing the EHZ capacity is NP-hard" Proc. AMS Series B - complexity result
9. **arXiv:2509.19083:** "A Bound on the Symplectic Systolic Ratio of Polytopes" - systolic bounds

### Secondary Sources

10. **Artstein-Avidan & Ostrover 2014:** "Bounds for Minkowski Billiard Trajectories" IMRN 2014(1):165-193 - billiard bounds
11. **Artstein-Avidan, Karasev & Ostrover 2014:** "From Symplectic Measurements to the Mahler Conjecture" Duke Math. J. 163:2003-2022 - Mahler connection
12. **Chaidez & Hutchings 2021:** "Computing Reeb dynamics on 4d convex polytopes" J.Comp.Dyn. 8(4):403-445 - computational methods
13. **Symplectic Capacities Project:** kylersiegel.xyz/EHZ/ - computational results (ICERM/TAU workshop 2015)

---

## Document Status

### Values with Strong Literature Support (Proven)
- Unit ball B^4: c = pi (normalization axiom)
- Tesseract [-1,1]^4: c = 4.0 (multiple sources)
- Pentagon counterexample: c = 3.4410 (HK-O 2024, Prop 1.4)
- Standard simplex: c = 1/(2n) (Nir 2013)

### Values with Computational Support
- Triangle x Triangle: c = 1.5 (algorithm agreement, Viterbo holds per Rudolf 2022)
- Regular n-gon products: approaches pi as n -> infinity

### Values with Bounds Only
- Cross-polytope / 16-cell: c <= sqrt(3) (arXiv:2509.19083)

### Values Not Found
- 24-cell (no symplectic literature found)
- Octahedron x octahedron (closed form)
- Hexagon x hexagon (closed form)
- Pentagon x Pentagon (same orientation, not rotated)

---

## Appendix A: Computing Pentagon Counterexample Values

### Pentagon Geometry (K = regular pentagon, circumradius 1)

Vertices at angles theta_k = 2*pi*k/5 for k=0,1,2,3,4:
```
v_k = (cos(theta_k), sin(theta_k))
```

Area:
```
A_K = (5/2) * sin(2*pi/5) = 2.37764129...
```

### Capacity Formula (HK-O 2024 Prop 1.4)

For T = K rotated by 90 degrees:
```
c_EHZ(K x T) = 2 * cos(pi/10) * (1 + cos(pi/5))
```

Numerical evaluation:
- cos(pi/10) = cos(18 deg) = 0.95105652...
- cos(pi/5) = cos(36 deg) = 0.80901699...
- c = 2 * 0.95105652 * 1.80901699 = 3.44095480...

### Systolic Ratio

```
Sys(K x T) = c^2 / (2 * Vol(K x T))
           = c^2 / (2 * A_K^2)
           = (sqrt(5) + 3) / 5
           = 1.04721359...
```

This exceeds 1, disproving Viterbo's conjecture.

---

## Appendix B: Standard Simplex Capacity

### Definition

The standard simplex in R^{2n} is:
```
Delta^{2n} = conv{0, e_1, e_2, ..., e_{2n}}
```

where e_i are the standard unit vectors.

### Capacity (Nir 2013)

```
c_EHZ(Delta^{2n}) = 1/(2n)
```

### Systolic Ratio Bound (arXiv:2509.19083)

For any simplex S in R^{2n}:
```
sys(S) <= (2n)! / (n! * (2n)^n)
```

This bound is asymptotically 0 and is tight. For R^4 (n=2): sys(S) <= 3/4.

### Asymptotic Behavior

The capacity of a simplex grows at most linearly in dimension, with coefficient approaching 2/e^2 in the large-dimension limit.
