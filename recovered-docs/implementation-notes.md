# Implementation Notes (2026-01-26)

Rough notes from spec review session. Feel free to discard if not useful — the spec itself is the source of truth.

## Context on Today's Fixes

These might help if you hit related issues:

### Closure Condition

Changed from checking one index to two. If you see `NoValidOrbits` everywhere, double-check the closure logic in `is_closed()`.

### Flow Map Normals

I changed which normals are used for trivialization. If fixed points don't work or orbits don't close, this is a good place to look. The key idea: use `exit_normal` from TwoFaceEnriched, not raw facet normals.

### Minimum Length Claim

I wrote "length ≥ 5" in the spec. My reasoning: can't cross same 2-face twice in opposite directions (ω antisymmetry). Might be wrong — verify if it matters for your implementation.

## Quick Ideas

**Cross-polytope check:** I added a test but didn't run it. Quick sanity check for one pair of adjacent normals:
- n_i = (1,1,1,1)/2, n_j = (1,1,1,-1)/2
- ω(n_i, n_j) = -0.5 ≠ 0 ✓

Suggests no Lagrangian 2-faces, but full verification needed.

**Build order that might work:**
1. Primitives (vectors, symplectic form)
2. H-rep + validation
3. 2-face enumeration
4. Trivialization
5. Root tubes → extension → closure → fixed points
6. Full algorithm

**Old code reference:** `git show v0.1.0-archive:packages/rust_viterbo/` has the old buggy implementation. Might be useful for structure, but don't trust its logic.

## Not Covered Here

The spec (Section 5) has the implementation guide with escalation boundaries, checkpoints, etc. Read that first.
