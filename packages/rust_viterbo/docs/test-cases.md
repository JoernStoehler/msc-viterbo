# Capacity Algorithm Test Cases

Reference document for validated test cases and expected values.

## Base Polytopes

### Tesseract (Hypercube) [-1,1]⁴

- **Structure**: Lagrangian product [-1,1]² × [-1,1]²
- **Facets**: 8 (4 q-facets, 4 p-facets)
- **Expected capacity**: 4.0
- **Literature**: Tesseract capacity is well-known; HK2019 cites this as a benchmark.
- **Algorithms**: HK2019 ✓, Billiard ✓, Tube ✓
- **Status**: Cross-validated, all three algorithms agree.

### Standard Simplex in ℝ⁴

- **Structure**: conv{0, e₁, e₂, e₃, e₄} (NOT Lagrangian product)
- **Facets**: 5
- **Expected capacity**: 1/(2n) = 1/4 = 0.25 for normalized simplex
- **Literature**: Haim-Kislev thesis (2019), formula c = 1/(2n) for standard simplex in ℝ^{2n}
- **Algorithms**: HK2019 ✓
- **Notes**:
  - Standard simplex with vertices at 0 and unit vectors has edge length 1.
  - Our test simplex (circumradius 1) gives capacity ~1.0.
  - Scaling by λ gives capacity λ² × original (verified: scale by 0.5 → capacity 0.25).

### HK-O 2024 Pentagon Product

- **Structure**: Lagrangian product K × T where K = regular pentagon, T = K rotated by 90°
- **Facets**: 10 (5 q-facets, 5 p-facets)
- **Expected capacity**: 2·cos(π/10)·(1+cos(π/5)) ≈ 3.441
- **Literature**: Haim-Kislev & Ostrover 2024, Proposition 1
- **Algorithms**: Billiard ✓ (after adjacent vertex fix)
- **Notes**:
  - HK2019 times out (10! = 3.6M permutations)
  - This is a COUNTEREXAMPLE to Viterbo's conjecture (systolic ratio > 1)
- **Data**: `packages/python_viterbo/data/counterexamples/hk-o-2024/`

## Lagrangian Product Test Cases

### Rectangle × Rectangle

| K₁ | K₂ | Expected | Billiard | HK2019 | Status |
|----|----|---------:|--------:|-------:|--------|
| [-1,1]² | [-1,1]² | 4.0 | 4.0 | ~4.0 | ✓ |
| [-1,1]×[-0.5,0.5] | same | 1.0 | 1.0 | ~1.0 | ✓ |

### Regular Polygon × Same Polygon (unrotated)

| Polygon | Facets | Billiard (heuristic) | Billiard (LP) | HK2019 | Status |
|---------|-------:|---------:|--------:|-------:|--------|
| Square | 8 | 4.0 | 4.0 | ~4.0 | ✓ |
| Hexagon | 12 | 4.0 | (TBD) | (too large) | Billiard only |
| Pentagon | 10 | 5.0 | (TBD) | (too large) | Billiard only |
| Triangle | 6 | 2.25 | **1.5** | 1.5 | ✓ |

**RESOLVED**: Triangle × triangle capacity is **1.5** (not 2.25). The heuristic algorithm
searches only at edge midpoints (Fagnano orbit), which is optimal for Euclidean billiards
but NOT for Minkowski billiards. The LP-based algorithm proves the optimal is at t=1/3.
See [billiard-correctness-proof.md](billiard-correctness-proof.md) Section 9.

## Scaling Axiom Tests

Capacity scales as λ² with size: c(λK) = λ²·c(K)

| Base | Scale λ | Expected | Computed | Status |
|------|--------:|--------:|--------:|--------|
| Tesseract | 2 | 16.0 | 16.0 | ✓ |
| Simplex | 0.5 | 0.25 | 0.25 | ✓ |

## Monotonicity Axiom Tests

If K ⊆ L, then c(K) ≤ c(L).

Tested by comparing nested polytopes. ✓

## Perturbation Tests

Small perturbations should give approximately equal capacity.

- Perturbed tesseract (random noise ε=1e-6): capacity within 1e-3 of original ✓

## Algorithm Limits

| Algorithm | Max Facets | Notes |
|-----------|-----------|-------|
| HK2019 | 8 practical, 10 max | O(F!) complexity, 60s timeout |
| Billiard | unlimited | O(n²) for Lagrangian products only |
| Tube | 8 typical | Often fails (no valid orbits) |

## Open Issues

### Triangle × Triangle Discrepancy (FULLY RESOLVED)

**Original Observation**:
- Heuristic billiard algorithm = 2.25, HK2019 = 1.5 (ratio 1.5)

**Resolution**: The **correct capacity is 1.5**. The heuristic algorithm was wrong.

**Root Cause**:

The heuristic billiard algorithm searches at edge midpoints (t=0.5), finding the **Fagnano orbit**.
The Fagnano orbit is optimal for **Euclidean** billiards, but NOT for **Minkowski** billiards.

For Minkowski billiards with K₂ = K₁ (equilateral triangle), the optimal is at t = 1/3
(one-third points on each edge), giving T-length = 1.5.

**Verification**:
- LP-based algorithm (billiard_lp.rs) proves minimum is 1.5 via linear programming
- Analytical verification: T-length at t=1/3 is 3 × 0.5 = 1.5
- HK2019 also gives 1.5, confirming correctness

**Why the Fagnano orbit (t=0.5) is NOT optimal**:
- Fagnano minimizes Euclidean length by using "reflection" points
- Minkowski billiards minimize support-function-weighted length
- Different objectives → different optima

See [billiard-correctness-proof.md](billiard-correctness-proof.md) Section 7 and Section 9
for the complete mathematical analysis.

### Tube Algorithm Limitations

Tube algorithm often returns NoValidOrbits because:
- Closure candidates don't satisfy rotation constraint (need rotation = 1.0)
- Only works for polytopes with favorable 2-face structure
- Rotated tesseract: 8 non-Lagrangian 2-faces found, but rotation ~1.75

## References

- Haim-Kislev (2019): "On the Symplectic Size of Convex Polytopes" - HK2019 formula
- Rudolf (2022): "The Minkowski Billiard Characterization of the EHZ-Capacity of Convex Lagrangian Products"
- Haim-Kislev & Ostrover (2024): "A Counterexample to Viterbo's Conjecture"
