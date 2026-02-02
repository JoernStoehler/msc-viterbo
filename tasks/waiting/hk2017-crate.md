# hk2017 Crate Implementation

**Priority:** P1
**Milestone:** M1 (Code Correctness)
**Blocked by:** geom4d symplectic_form, reeb_vector, Characteristic

## Goal

Implement HK2017 algorithm for computing EHZ capacity of general convex polytopes.

## Algorithm Overview

HK2017 computes capacity by:
1. Enumerate all closed characteristics (facet cycles)
2. For each characteristic, compute action
3. Capacity = minimum action over all characteristics

## Features to Implement

- [ ] `enumerate_characteristics` — Find all closed characteristics
- [ ] `characteristic_action` — Compute action of a characteristic
- [ ] `ehz_capacity` — Main entry point

## Performance Characteristics

From `docs/learnings/hk2017-performance.md`:
- Runtime: `time_ms ≈ 5.51e-04 × perms^1.059`
- Practical limit: F ≤ 8 facets (naive), F ≤ 10 (graph-pruned)
- O(F!) complexity without pruning

## Dependencies

- geom4d: HRep, Characteristic, is_closed, action
- Reference implementation: git show 0b5511a:packages/rust_viterbo/hk2017/

## Notes

- Legacy code at commit 0b5511a has working implementation
- Focus on correctness first, optimization later
- Graph pruning can reduce search space significantly
