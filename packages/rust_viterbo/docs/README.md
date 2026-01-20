# Rust Viterbo Documentation

Documentation for the `rust_viterbo` crate - EHZ capacity computation for convex polytopes.

---

## Quick Navigation

### Source of Truth Documents

| Document | Purpose | When to Read |
|----------|---------|--------------|
| **[mathematical-claims.md](mathematical-claims.md)** | All mathematical claims with citations | Adding math, verifying correctness |
| **[test-documentation.md](test-documentation.md)** | Test organization and status | Running tests, adding tests |
| **[test-cases.md](test-cases.md)** | Test polytopes and expected values | Adding test fixtures |
| **[code-audit-tracker.md](code-audit-tracker.md)** | Current implementation status | Understanding what works/broken |

### Algorithm Specifications

| Document | Purpose | When to Read |
|----------|---------|--------------|
| [algorithm-spec.md](algorithm-spec.md) | Tube algorithm implementation | Working on tube algorithm |
| [algorithm-billiard-spec.md](algorithm-billiard-spec.md) | Billiard algorithm for Lagrangian products | Working on billiard |
| [algorithm-hk2019-spec.md](algorithm-hk2019-spec.md) | HK2019 QP algorithm | Working on HK2019 |
| [tube-geometry-spec.md](tube-geometry-spec.md) | Geometric formulas for tube algorithm | Tube geometry questions |

### Other

| Document | Purpose |
|----------|---------|
| [ffi-contract.md](ffi-contract.md) | Python FFI contract |
| [test-propositions.md](test-propositions.md) | Detailed mathematical test propositions |
| [archive/](archive/) | Superseded documentation |

---

## Document Hierarchy

```
docs/
├── README.md                    <- You are here
│
├── SOURCES OF TRUTH
│   ├── mathematical-claims.md   <- All math claims with citations
│   ├── test-documentation.md    <- Test organization
│   ├── test-cases.md            <- Test fixtures
│   └── code-audit-tracker.md    <- Current status
│
├── ALGORITHM SPECS
│   ├── algorithm-spec.md        <- Tube algorithm
│   ├── algorithm-billiard-spec.md <- Billiard algorithm
│   ├── algorithm-hk2019-spec.md <- HK2019 algorithm
│   └── tube-geometry-spec.md    <- Tube geometry
│
├── OTHER
│   ├── ffi-contract.md          <- FFI contract
│   └── test-propositions.md     <- Detailed test propositions
│
└── archive/                     <- Superseded docs
    ├── README.md
    ├── test-spec.md
    ├── test-improvement-plan.md
    └── billiard-correctness-proof.md
```

---

## Key Conventions

### Adding Mathematical Claims

1. Add to `mathematical-claims.md` first
2. Include: statement, citation (paper + theorem), verification status
3. If uncited, mark as `[UNCITED - NEEDS VERIFICATION]`
4. Reference from code docstrings

### Adding Tests

1. Find the right topic file in `algorithm/src/tests/`
2. Add fixture to `fixtures.rs` if needed
3. Update `test-cases.md` with expected values
4. Use `#[ignore = "reason"]` for blocked tests

### Documenting Known Issues

Use `code-audit-tracker.md` for:
- Implementation status
- Known bugs
- Test coverage gaps

---

## Current Status (2026-01-20)

### What Works
- **Billiard (LP):** Correct for tesseract, triangle. Pentagon has bug.
- **HK2019:** Works but QP solver incomplete. Tests pass by luck.
- **Tube:** Runs but returns NoValidOrbits for all tested polytopes.

### Known Bugs
1. Pentagon capacity: returns 2.127, expected 3.441
2. HK2019 QP: only checks 0D/1D faces
3. Witness segment_times: not implemented

### Test Status
- 186+ tests, 13 ignored (documented reasons)

For details, see `code-audit-tracker.md`.

---

## Related Documentation

- Thesis: `packages/latex_viterbo/`
- Python experiments: `packages/python_viterbo/`
- Session handoffs: `scratch/`
