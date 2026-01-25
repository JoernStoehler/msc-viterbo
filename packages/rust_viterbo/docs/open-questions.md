# Open Questions: developer-spec-v2.md

**Date:** 2026-01-25
**Purpose:** Questions requiring project owner input before implementation.

---

## 1. Trivialization Normal Convention (Critical)

### The Question

The spec says: "Use the **exited facet's normal** (the facet we're leaving)."

CH2021 Definition 2.15 says: "Let ν denote the **outward unit normal vector to E**" where E is "the unique 3-face adjacent to F such that the Reeb vector field R_E **points into E from F**."

**These appear to be opposite conventions:**
- Spec: normal of facet we're *leaving* (entry facet)
- CH2021: normal of facet we're *entering* (exit facet)

### Evidence from CH2021

From `docs/papers/s2_type_1_reeb_orbits.tex` lines 188-207:

> "By Lemma~\ref{lem:Reebcone}, there is a unique $3$-face $E$ adjacent to $F$ such that the Reeb cone $R_F^+$ consists of the nonnegative multiples of the Reeb vector field $R_E$, and the latter **points into $E$ from $F$**. Let $\nu$ denote the **outward unit normal vector to $E$**."

The facet E is the one the flow is going INTO. Its outward normal ν is used for trivialization.

### Impact

If the spec has the wrong convention:
- Transition matrices would be inverted
- Flow directions could be wrong
- Rotation numbers could have wrong sign

### Request

Please verify: Which facet's normal should we use for trivialization at a 2-face F_{i,j}?
- (A) The facet we just left (spec's current interpretation)
- (B) The facet we're about to enter (CH2021's convention)

---

## 2. Transition Matrix Direction

### The Question

The spec (§1.11) defines: **ψ_F = τ_{n_j} ∘ τ_{n_i}^{-1}**

CH2021 Definition 2.17 defines: **ψ_F = τ_F ∘ (τ_F')^{-1}**

where τ_F uses the EXIT facet's normal ν, and τ_F' uses the ENTRY facet's normal ν'.

### Interpretation

If F_{i,j} is a 2-face with flow direction i → j:
- Entry facet = i, exit facet = j
- τ_F uses n_j (exit), τ_F' uses n_i (entry)
- So CH2021's ψ_F = τ_{n_j} ∘ τ_{n_i}^{-1}

This **matches** the spec's definition, but only if:
- i is the entry facet (we came from i)
- j is the exit facet (flow goes toward j)

### Consistency Check Needed

The convention depends on whether [i, j] means:
- (A) "entered from i, about to flow along j toward some k" → i is entry, j is where we are
- (B) Something else

Please confirm the relationship between facet_sequence semantics and transition matrix direction.

---

## 3. entry_normal Field Semantics

### Current State

I added `entry_normal: Vector4<f64>` to `TwoFaceEnriched` with comment:
> "n_i or n_j depending on flow direction"

### Problem

Given the confusion in Q1-Q2, I'm not confident this field is correctly specified.

For a 2-face F_{i,j} (where i < j by convention):
- Flow direction could be i→j or j→i depending on sign of ω(n_i, n_j)
- Which normal is "entry" depends on flow direction
- The field might need to be computed, not stored

### Request

Should this field:
- (A) Store the entry facet's normal (used for alternate convention τ_F')
- (B) Store the exit facet's normal (used for main convention τ_F)
- (C) Be removed in favor of computing on-demand from flow direction
- (D) Something else

---

## 4. Action Function Derivation (Minor)

### Current State

The spec says (§2.9):
> "Why action is affine in starting position: The action formula A(γ) = (1/2)∫⟨Jγ, γ̇⟩dt is translation-invariant..."

### Problem

This argument conflates continuous contact geometry with discrete polytope geometry. The actual proof is:

1. Each segment's exit time is **linear** in its starting point (from solving the exit hyperplane equation)
2. Affine composition of affine functions preserves affinity
3. Sum of affine functions is affine

### Request

Replace hand-wavy argument with cleaner derivation? Low priority since the conclusion is correct.

---

## Resolved Questions

### Quaternion Choice (Resolved)

Q: Why J, K specifically?

A: They are the canonical quaternionic left-multiplication operators. CH2021 Lemma 2.16 proves ω₀(j·ν, k·ν) = 1, which is why the trivialization preserves the symplectic form. Properly cited.

### Root Tube Semantics (Resolved, needs doc improvement)

Q: What does facet_sequence = [i, j] mean?

A: "At 2-face F_{i,j}, entered facet j from facet i, about to flow along j."

The code is consistent with this. Minor doc improvement: move the semantic definition from Handoff Notes to the Tube struct definition itself.

---

## Summary

| Question | Blocking? | Request |
|----------|-----------|---------|
| Q1: Trivialization normal | **Yes** | Verify entry vs exit convention |
| Q2: Transition matrix direction | **Yes** | Confirm consistency with Q1 |
| Q3: entry_normal field | **Yes** | Define semantics after Q1-Q2 resolved |
| Q4: Action derivation | No | Optional improvement |
