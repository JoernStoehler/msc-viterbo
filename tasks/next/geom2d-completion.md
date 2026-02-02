# geom2d Crate Completion

**Priority:** P1
**Milestone:** M1 (Code Correctness)

## Goal

Complete the geom2d crate with all primitives needed for billiard algorithm.

## Current State

- ✅ `Polygon` — CCW convex with validation
- ✅ `area()` — Shoelace formula with proof

## Remaining Features

### Foundation
- [ ] `polygon_intersection` — Sutherland-Hodgman algorithm
- [ ] `point_in_polygon` — Convex case (half-plane test)

### For Billiard Algorithm
- [ ] `reflect_point` — Reflection across polygon edge
- [ ] `billiard_trajectory` — Compute trajectory segments

## Proof-First Workflow

Each feature follows stages 1-7:
1. Terminology
2. Computable definitions
3. Lemmas with proofs [proposed] → [verified]
4. Signatures
5. Test brainstorming
6. Test implementation
7. Implementation

## Dependencies

None — geom2d is foundational.

## Notes

- Coordinate system: standard Cartesian (x right, y up)
- All polygons stored CCW with validated convexity
- Tolerances in `tolerances.rs`
