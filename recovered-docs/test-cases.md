# Capacity Algorithm Test Cases

Catalog of test polytopes with expected values and verification status.

For test infrastructure and running tests, see `test-documentation.md`.
For mathematical claims and citations, see `mathematical-claims.md`.

---

## Base Polytopes

### Tesseract (Hypercube) [-1,1]^4

| Property | Value |
|----------|-------|
| Structure | Lagrangian product [-1,1]^2 x [-1,1]^2 |
| Facets | 8 (4 q-facets, 4 p-facets) |
| Expected capacity | 4.0 |
| Citation | HK2019 Example 4.6; Rudolf 2022 Example 3.5 |
| Billiard | 4.0 (verified) |
| HK2019 | 4.0 (verified) |
| Tube | NoValidOrbits (Lagrangian, expected) |
| Status | Cross-validated |

---

### Equilateral Triangle x Triangle

| Property | Value |
|----------|-------|
| Structure | Lagrangian product, circumradius 1 |
| Facets | 6 (3 q-facets, 3 p-facets) |
| Expected capacity | 1.5 |
| Citation | [UNCITED - computational verification only] |
| Billiard (LP) | 1.5 (verified) |
| HK2019 | 1.5 (verified) |
| Status | Cross-validated |

**Note:** The Fagnano orbit (t=0.5) gives 2.25, but the optimal Minkowski trajectory is at t=1/3.

---

### Pentagon x Rotated Pentagon (HK-O Counterexample)

| Property | Value |
|----------|-------|
| Structure | K x T where K = regular pentagon, T = K rotated 90 degrees |
| Facets | 10 (5 q-facets, 5 p-facets) |
| Expected capacity | 2*cos(pi/10)*(1+cos(pi/5)) = 3.4409548... |
| Citation | Haim-Kislev & Ostrover 2024, Proposition 1 |
| Billiard | [BUG] Returns 2.127 = expected/phi |
| HK2019 | Times out (10! permutations) |
| Status | **BUG - under investigation** |

This is a COUNTEREXAMPLE to Viterbo's conjecture (systolic ratio > 1).

Data: `packages/python_viterbo/data/counterexamples/hk-o-2024/`

---

### Rectangle [-1,1] x [-0.5,0.5]

| Property | Value |
|----------|-------|
| Structure | Lagrangian product |
| Facets | 8 |
| Expected capacity | 1.0 (4 * min(1, 0.5)^2) |
| Billiard | 1.0 (verified) |
| HK2019 | ~1.0 (verified) |
| Status | Cross-validated |

---

### Standard Simplex in R^4

| Property | Value |
|----------|-------|
| Structure | conv{0, e_1, e_2, e_3, e_4} - NOT Lagrangian product |
| Facets | 5 |
| Expected capacity | 1/(2n) = 0.25 for normalized simplex |
| Citation | [UNCITED - needs verification from HK thesis] |
| Billiard | N/A (not Lagrangian) |
| HK2019 | Not tested |
| Status | **NOT TESTED** |

---

## Axiom Tests

### Scaling: c(lambda K) = lambda^2 c(K)

| Base | Scale | Expected | Computed | Status |
|------|-------|----------|----------|--------|
| Tesseract | 2 | 16.0 | 16.0 | Verified |
| Random products | [0.3, 3.0] | lambda^2 * c | lambda^2 * c | Proptest |

### Monotonicity: K subset L implies c(K) <= c(L)

Tested via proptest with random products and expansion factors [1.01, 2.0].

### Symplectomorphism Invariance

| Transform | Status |
|-----------|--------|
| Block rotation (q1,p1) | Tested |
| Block rotation (q2,p2) | Tested |
| Combined rotation | Tested |
| Shear | Ignored (breaks Lagrangian structure) |

---

## Algorithm Domain

| Algorithm | Lagrangian Products | General Polytopes | Max Facets |
|-----------|---------------------|-------------------|------------|
| Billiard (LP) | Works | N/A | Unlimited |
| HK2019 | Works | Works | 8 practical |
| Tube | Fails (degenerate) | Untested | N/A |

---

## Known Issues

1. **Pentagon capacity bug:** Returns 2.127, expected 3.441 (ratio = phi)
2. **HK2019 QP solver:** Only checks vertices/edges, may miss optimum on higher faces
3. **Tube algorithm:** Returns NoValidOrbits for all tested polytopes
4. **Witness segment_times:** Not implemented (placeholder zeros)

---

## References

- HK2019: Haim-Kislev 2019, "On the Symplectic Size of Convex Polytopes"
- Rudolf 2022: "The Minkowski Billiard Characterization of the EHZ-Capacity"
- HK-O 2024: Haim-Kislev & Ostrover 2024, "A Counterexample to Viterbo's Conjecture"
