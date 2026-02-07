# Finding: Full Orbit Validation Required

**Date:** 2026-01-26
**Status:** Fixed in commits `b5d43c9` and `05169c3`

## Summary

The billiard solver was returning invalid orbits because it only validated q-displacement achievability, not the full k-bounce orbit structure.

## The Bug

A k-bounce trajectory in a Lagrangian product K_q × K_p has **2k affine segments**, not k:

**2-bounce (4 segments):**
1. q at q₀ (q-facet): p moves from p_back to p_fwd
2. p at p_fwd (p-facet): q moves q₀ → q₁
3. q at q₁ (q-facet): p moves from p_fwd to p_back
4. p at p_back (p-facet): q moves q₁ → q₀

**3-bounce (6 segments):**
1. q at q₀: p moves p₂ → p₀
2. p at p₀: q moves q₀ → q₁
3. q at q₁: p moves p₀ → p₁
4. p at p₁: q moves q₁ → q₂
5. q at q₂: p moves p₁ → p₂
6. p at p₂: q moves q₂ → q₀

The old code only checked segments 2, 4, (6) - that the q-displacements are achievable by some Reeb velocity direction. It did NOT check segments 1, 3, (5) - that the p-transitions at each bounce are achievable.

## Example: Pentagon × Rotated Pentagon

For K = Pentagon × Pentagon(rotated 90°):
- Expected capacity: 2·cos(π/10)·(1 + cos(π/5)) ≈ 3.441 (diagonal v₀→v₂→v₀)
- Old code returned: ≈ 2.127 (invalid edge trajectory v₀→v₁→v₀)

The edge trajectory v₀→v₁→v₀ fails because:
- Forward motion (v₀→v₁) requires p at vertex w₃
- Backward motion (v₁→v₀) requires p at vertex w₀
- At bounce q=v₀: p must transition w₀ → w₃
- This Δp = (0.588, -1.809) is NOT in the allowed ṗ cone at v₀

The allowed ṗ directions at vertex v₀ (intersection of edges 4 and 0) form cone(W₄, W₀) where W_k = (2/h_k)·n_k. The required Δp has negative coefficient for W₄, so it's invalid.

## The Fix

Added `validate_2bounce_orbit` and `validate_3bounce_orbit` functions that:
1. Find where p must be during each q-motion phase
2. Compute the required Δp at each bounce
3. Check that each Δp is in the allowed ṗ cone (positive combination of the W_k vectors for the active q-edges)

## Key Insight

The spec says "differential inclusion is automatically satisfied when we use the T°-length formulation" (line 702). This is **partially true** for q-motion (the achievability check handles it), but **false** for p-motion at bounces - these must be explicitly validated.

## Files Changed

- `billiard/src/solve.rs`: Added orbit validation functions

## Tests

All 17 tests pass after the fix, including:
- `test_tesseract_capacity`: capacity = 4.0 ✓
- `test_pentagon_counterexample`: capacity ≈ 3.441 ✓
