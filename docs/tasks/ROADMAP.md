# Roadmap

## Task Flow (GTD-style)

```
inbox → next → waiting → review → done
```

| Directory | Meaning |
|-----------|---------|
| `inbox/` | New/uncategorized tasks |
| `next/` | Actively working on |
| `waiting/` | Blocked on dependency |
| `review/` | Agent done, awaiting Jörn review |
| `done/` | Jörn approved, truly complete |

Directory is source of truth for status. Move files to change status.

---

## Milestones

### M1: Code Correctness (Target: Feb 2026)

**Next:**
- [geom2d-completion](next/geom2d-completion.md) — Polygon, area, intersection
- [geom4d-completion](next/geom4d-completion.md) — HRep, is_bounded, symplectic, reeb, 2-faces

**Waiting:**
- [hk2017-crate](waiting/hk2017-crate.md) — Blocked by geom4d Characteristic
- [tube-crate](waiting/tube-crate.md) — Blocked by geom4d 2-faces, geom2d intersection
- [billiard-crate](waiting/billiard-crate.md) — Blocked by geom2d billiard trajectory

**Verification:**
- [ ] Cross-algorithm agreement on test polytopes
- [ ] Comparison with literature values

### M2: Thesis Draft (Target: Feb 2026)
- [ ] Algorithm chapter complete
- [ ] Experiment chapter complete
- [ ] Counterexample analysis ([counterexample-hko](waiting/counterexample-hko.md))

### M3: Final Submission (Target: Mar 2026)
- [ ] Advisor review addressed
- [ ] Final formatting

---

## Current Focus

Priority order:
1. **geom4d symplectic/reeb** — Unlocks HK2017
2. **geom4d 2-faces** — Unlocks tube
3. **geom2d intersection** — Unlocks tube capacity computation

## Dependency Graph

```
geom2d                    geom4d
  │                         │
  ├─ Polygon ✓              ├─ HRep ✓
  ├─ area ✓                 ├─ is_bounded ✓
  ├─ intersection ○         ├─ symplectic_form ○
  └─ billiard ○             ├─ reeb_vector ○
       │                    ├─ TwoFace ○
       │                    └─ Characteristic ○
       │                         │
       ▼                         ▼
   billiard              hk2017    tube
      ○                    ○        ○

✓ = done, ○ = todo
```

## Parking Lot

Ideas captured but not prioritized:
- [algorithm-comparison](waiting/algorithm-comparison.md) — Compare HK2017 vs tube vs billiard
- [polytope-database](waiting/polytope-database.md) — Systematic polytope enumeration
