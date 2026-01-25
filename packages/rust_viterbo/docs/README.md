# Rust Viterbo Documentation

Documentation for the `rust_viterbo` package - EHZ capacity computation for convex polytopes.

> **Status:** Ready for implementation. Previous code archived at tag `v0.1.0-archive`.

---

## Quick Navigation

| Document | Purpose | When to Read |
|----------|---------|--------------|
| **[developer-spec-v2.md](developer-spec-v2.md)** | **PRIMARY SPEC** — Tube algorithm specification | Implementing the algorithm |
| [open-questions.md](open-questions.md) | Resolved design questions with rationale | Understanding past decisions |
| [developer-spec.md](developer-spec.md) | DEPRECATED v1 spec (all three algorithms) | Historical reference only |
| [implementation-status.md](implementation-status.md) | Status of archived v0.1.0 implementation | Learning from past attempt |
| [mathematical-claims.md](mathematical-claims.md) | Mathematical claims with citations | Verifying correctness |
| [ffi-contract.md](ffi-contract.md) | Python FFI API contract | Calling from Python |

---

## Document Hierarchy

```
docs/
├── README.md                    <- You are here
│
├── SPECIFICATIONS
│   ├── developer-spec.md        <- All three algorithms
│   └── ffi-contract.md          <- Python API
│
├── MATHEMATICAL
│   ├── mathematical-claims.md   <- All math with citations
│   └── test-propositions.md     <- Claims → test mappings
│
├── STATUS
│   ├── implementation-status.md <- What worked/didn't
│   └── test-interpretation.md   <- What results mean
│
└── archive/                     <- Superseded docs
```

---

## Accessing Archived Source Code

The Rust implementation is preserved in git history:

```bash
# View archived files
git show v0.1.0-archive:packages/rust_viterbo/algorithm/src/billiard.rs

# Checkout archived code to a directory
git worktree add ../rust-viterbo-archive v0.1.0-archive

# Browse archived code interactively
git log --oneline v0.1.0-archive -- packages/rust_viterbo/
```

---

## Algorithm Summary

| Algorithm | Domain | Status (at archive) |
|-----------|--------|---------------------|
| **Billiard** | Lagrangian products K₁ × K₂ | ✅ WORKED (tesseract=4.0, triangle=1.5) |
| **Tube** | General polytopes | ⚠️ NoValidOrbits on all tested |
| **HK2019 QP** | Any polytope (≤10 facets) | ❌ INCOMPLETE (vertex+edge only) |

**Known Bug:** Pentagon × RotatedPentagon returns 2.127, expected 3.441.

For full algorithm specifications, see [developer-spec.md](developer-spec.md).

---

## FFI Stub

The FFI crate (`ffi/`) is an archived stub that returns `NotImplementedError` for all capacity functions. Only `symplectic_form_4d()` still works.

To implement:
1. Read [developer-spec-v2.md](developer-spec-v2.md) for the Tube algorithm specification
2. Read [ffi-contract.md](ffi-contract.md) for Python API
3. Optionally reference archived code via `git show v0.1.0-archive:packages/rust_viterbo/`

---

## Related Documentation

- **Thesis:** `packages/latex_viterbo/` (especially `chapters/algorithms.tex`)
- **Python experiments:** `packages/python_viterbo/`
