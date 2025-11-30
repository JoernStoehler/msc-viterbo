---
title: Literature Overview (Annotated Bibliography)
slug: literature-overview
summary: Canonical pointer list of which papers supply which facts for the thesis; synced with the archived reading plan.
---

# Literature Overview (Annotated Bibliography)

Purpose: quick lookup of which papers provide which facts for the thesis (math intro + algorithms). Keep this synced with the archived reading plan at `packages/thesis/archive/msc-proto/briefs/2025-10-12-workflow-reading-list.md`.

Paper download helper (immutable store + per-worktree extract):
```bash
# replace <id>vN with the explicit arXiv version shown on the paper page
ARXIV_STORE=/workspaces/worktrees/shared/arxiv-store \
  packages/thesis/scripts/arxiv_fetch.sh -p <id>vN <id2>vM
```

## Core statements and dualities
- **Viterbo (2000)** — Defines normalized symplectic capacities and states the isoperimetric/systolic conjecture; source for the axioms we cite and the normalizations we adopt.
- **Artstein-Avidan, Karasev, Ostrover (2013/14)** — Relates Viterbo-type bounds to Mahler’s volume product; gives duality heuristics for $K \times K^\circ$ that guide our Lagrangian product tests.
- **Artstein-Avidan & Ostrover (2007/08)** — Brunn–Minkowski inequality for symplectic capacities; supplies monotonicity/concavity intuition we use when comparing families of polytopes.
- **Vicente (2025)** — Shows all normalized capacities coincide for certain dual Lagrangian products and proves a strong Viterbo bound under Young-function hypotheses; we reuse the normalisation coincidences as a consistency check.

## Counterexamples and structural constraints
- **Haim-Kislev & Ostrover (2024)** — First explicit counterexample to Viterbo’s conjecture in $4$D via a Lagrangian product of rotated pentagons; anchors our “must-handle” test instance and motivates supporting Lagrangian $2$-faces.
- **Haim-Kislev (2017)** — Combinatorial formula/simple-loop property for the EHZ capacity on convex bodies; justifies restricting the search to facet-simple closed characteristics in our algorithm.

## Algorithms and computation (polytopes)
- **Chaidez & Hutchings (2020/21)** — Combinatorial algorithm for Reeb dynamics on $4$D convex polytopes; provides the rotation bound $\rho<2$ and the no-$1$-face-segment rule used in our pruning.
- **Krupp (2020)** — PhD thesis with LP/SOCP/SDP formulations and practical code guidance for computing $c_{\mathrm{EHZ}}$ on polytopes; baseline for optimisation-based upper/lower bounds.
- **Rudolf (2022/24)** — Minkowski billiard characterisation of $c_{\mathrm{EHZ}}(K \times T)$; supplies an alternate algorithmic route for Lagrangian products and sanity checks against our search results.
- **Leipold & Vallentin (2024)** — Proves computing $c_{\mathrm{EHZ}}$ is NP-hard; frames our expectations about worst-case behaviour and motivates heuristics and caching.

## Equality cases and geometric bounds
- **Balitskiy (2015)** — Classifies equality cases for Viterbo via billiard trajectories; we cite it when discussing sharpness and candidate extremisers.

## Index and variational tools
- **Long (2002, book)** — Standard reference for Conley–Zehnder index iteration; background for translating the CH rotation bound and for any index-based pruning arguments in the math intro.

## Notes and usage
- Cite the paper that actually supplies each fact; avoid inventing terminology. When in doubt, prefer the canonical source above over surveys.
- When adding new references, extend the archive brief and this page together so priorities/effort tags stay aligned.
- Add per-paper digests in `packages/thesis/src/literature/` using the template in `packages/thesis/docs/workflows.md`.
