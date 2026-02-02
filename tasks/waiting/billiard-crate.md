# billiard Crate Implementation

**Priority:** P2
**Milestone:** M1 (Code Correctness)
**Blocked by:** geom2d polygon_intersection, reflect_point, billiard_trajectory

## Goal

Implement billiard algorithm for computing EHZ capacity of Lagrangian product polytopes.

## Algorithm Overview

For Lagrangian products K = K₁ × K₂ (where K₁, K₂ are 2D convex):
1. Project 4D characteristic to 2D billiard trajectory
2. Simulate billiard bouncing between K₁ and K₂ boundaries
3. Compute action from trajectory length
4. Capacity = 4 × area(K₁) × area(K₂) / action

## Features to Implement

- [ ] `is_lagrangian_product` — Check if polytope is K₁ × K₂
- [ ] `extract_factors` — Get K₁, K₂ from product
- [ ] `billiard_orbit` — Compute periodic billiard orbit
- [ ] `orbit_action` — Action of billiard orbit
- [ ] `ehz_capacity` — Main entry point

## Performance Characteristics

- O(E^6) where E = edges in K₁ + K₂
- No practical facet limit
- Much faster than HK2017 for Lagrangian products

## Dependencies

- geom2d: Polygon, reflect_point, billiard_trajectory, area
- geom4d: HRep (for is_lagrangian_product check)
- Reference implementation: git show 0b5511a:packages/rust_viterbo/billiard/

## Notes

- Specialized for Lagrangian products only
- Falls back to tube algorithm for non-Lagrangian
- Legacy spec at commit 0b5511a (draft state)
