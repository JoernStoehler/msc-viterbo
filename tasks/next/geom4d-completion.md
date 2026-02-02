# geom4d Crate Completion

**Priority:** P0
**Milestone:** M1 (Code Correctness)

## Goal

Complete the geom4d crate with all primitives needed for HK2017 and tube algorithms.

## Current State

- ✅ `HRep` — H-representation with validation
- ✅ `is_bounded()` — LP-based boundedness check

## Remaining Features

### Foundation (P0)
- [ ] `symplectic_form` — ω(u,v) = ⟨Ju, v⟩ where J is standard symplectic matrix
- [ ] `reeb_vector` — R_i = (2/h_i) J n_i for facet i

### 2-Faces (P0 — needed for tube algorithm)
- [ ] `TwoFace` — Intersection of two facets
- [ ] `is_lagrangian` — Check if ω(n_i, n_j) = 0
- [ ] `flow_direction` — Which facet flows to which
- [ ] `adjacency` — Which facets share 2-faces

### Characteristics (P1 — needed for HK2017)
- [ ] `Characteristic` — Ordered facet sequence with weights
- [ ] `is_closed` — Σ β_i n_i = 0
- [ ] `action` — Σ β_i h_i

## Proof-First Workflow

Each feature follows stages 1-7. Math definitions from thesis Chapter 2.

## Dependencies

- Depends on: nalgebra, good_lp
- Depended on by: hk2017, tube

## Notes

- All normals are outward unit normals
- Heights h_i > 0 (distance from origin to facet)
- Symplectic form uses standard J = [[0, -I], [I, 0]]
