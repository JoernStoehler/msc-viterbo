# Open Questions: developer-spec-v2.md

**Date:** 2026-01-25
**Purpose:** Questions requiring project owner input before implementation.

---

## Open Questions

*None currently open.*

---

## Resolved Questions

### Q4: Action Function Derivation (Resolved 2026-01-25)

**Question:** The spec's argument for "action is affine in starting position" was hand-wavy.

**Resolution:** Replaced with elementary algebraic proof:
1. Reeb flow is linear: p(t) = p₀ + t·R
2. Exit time is affine in p₀ (solve hyperplane equation)
3. Segment action = segment time (for Reeb flow)
4. Composition of affine functions is affine (by induction, all breakpoints are affine in initial position)
5. Sum of affine functions is affine

**Spec update:** Section 2.9 now has the correct 5-step derivation.

### Q1: Trivialization Normal Convention (Resolved 2026-01-25)

**Question:** Which facet's normal for trivialization: entry (n_i) or exit (n_j)?

**Resolution:** Follow CH2021 Definition 2.15 — use the **exit facet's normal** (n_j for flow i → j).

CH2021 states: "Let ν denote the outward unit normal vector to E" where E is the facet the Reeb flow **points into**.

**Spec update:** TwoFaceEnriched now stores both `entry_normal` (n_i, for debugging) and `exit_normal` (n_j, PRIMARY per CH2021). The `polygon_2d` uses exit_normal.

### Q2: Transition Matrix Direction (Resolved 2026-01-25)

**Question:** Does spec's ψ_F = τ_{n_j} ∘ τ_{n_i}^{-1} match CH2021?

**Resolution:** Yes, it matches. CH2021's ψ_F = τ_F ∘ (τ_F')^{-1} where:
- τ_F uses exit facet's normal (n_j)
- τ_F' uses entry facet's normal (n_i)

For flow [i → j], this gives ψ_F = τ_{n_j} ∘ τ_{n_i}^{-1}, which is exactly what the spec says.

### Q3: entry_normal Field Semantics (Resolved 2026-01-25)

**Question:** What should the entry_normal field store?

**Resolution:** Keep **both** normals for debugging:
- `entry_normal: Vector4<f64>` — n_i (entry facet), for debugging/verification
- `exit_normal: Vector4<f64>` — n_j (exit facet), PRIMARY per CH2021

The `polygon_2d` field uses `exit_normal` for trivialization (CH2021 convention).

### Quaternion Choice (Resolved)

**Question:** Why J, K specifically?

**Resolution:** They are the canonical quaternionic left-multiplication operators. CH2021 Lemma 2.16 proves ω₀(j·ν, k·ν) = 1, which is why the trivialization preserves the symplectic form. Properly cited.

### Root Tube Semantics (Resolved)

**Question:** What does facet_sequence = [i, j] mean?

**Resolution:** "At 2-face F_{i,j}, entered facet j from facet i, about to flow along j."

The code is consistent with this. Doc improvement: semantic definition added to Handoff Notes in spec.

---

## Summary

| Question | Status | Resolution |
|----------|--------|------------|
| Q1: Trivialization normal | **Resolved** | Use exit facet (n_j) per CH2021 |
| Q2: Transition matrix direction | **Resolved** | Spec matches CH2021 |
| Q3: entry_normal field | **Resolved** | Store both; polygon_2d uses exit_normal |
| Q4: Action derivation | **Resolved** | Elementary algebraic proof in §2.9 |

**All questions resolved as of 2026-01-25.**
