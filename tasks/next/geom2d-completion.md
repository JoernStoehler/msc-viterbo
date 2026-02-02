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

Each feature follows stages 1-7. See proof-first-workflow skill for details.

Markers:
- `[proposed]` = agent-written, awaiting Jörn review
- `[verified]` = Jörn has confirmed correctness

## Dependencies

None — geom2d is foundational.

## Labor Estimate

- **AI labor:** Moderate (4 features, standard algorithms)
- **Human help:** Low (verify proofs in doc comments)

## Notes

- Coordinate system: standard Cartesian (x right, y up)
- All polygons stored CCW with validated convexity
- Tolerances in `tolerances.rs`
