# tube Crate Implementation

**Priority:** P1
**Milestone:** M1 (Code Correctness)
**Blocked by:** geom4d TwoFace, is_lagrangian, flow_direction, adjacency; geom2d polygon_intersection

## Goal

Implement tube algorithm for computing EHZ capacity of non-Lagrangian polytopes.

## Algorithm Overview

For non-Lagrangian polytopes, the tube algorithm:
1. Build adjacency graph of 2-faces
2. Find flow direction on each 2-face (via Reeb vector)
3. Construct tubes (sequences of 2-faces following flow)
4. Compute capacity of each tube via 2D polygon intersection
5. Capacity = minimum over all tubes

## Features to Implement

- [ ] `build_adjacency_graph` — 2-face adjacency
- [ ] `compute_flow_directions` — Reeb flow on 2-faces
- [ ] `enumerate_tubes` — Find all tube sequences
- [ ] `tube_capacity` — Capacity of single tube
- [ ] `ehz_capacity` — Main entry point

## Performance Characteristics

From capacity-algorithms skill:
- Runtime: ~1.6µs per tube
- Scales well to F = 16+ facets
- Hotspots: tube_capacity (24-33%), intersect_polygons (12-16%)

## Dependencies

- geom4d: HRep, TwoFace, is_lagrangian, flow_direction, adjacency
- geom2d: Polygon, polygon_intersection, area
- Reference implementation: git show 0b5511a:packages/rust_viterbo/tube/

## Notes

- Only works for non-Lagrangian polytopes
- Use HK2017 for Lagrangian polytopes
- Legacy code at commit 0b5511a
