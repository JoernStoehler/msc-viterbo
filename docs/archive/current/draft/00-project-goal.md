# Probing Viterbo's Conjecture – Overview

## Status and Scope
This file is the high-level outline and single source of truth for the project. We move fast: documentation always targets the latest commit; older commits are deprecated immediately. There is no stable API and breaking changes are not announced. The wording below is intended to be literal and unambiguous.

## Project Context
MSc thesis of Jörn Stöhler, supervised by Prof. Kai Cieliebak (University of Augsburg). The thesis probes Viterbo's conjecture in symplectic geometry using computational methods.

## Components
- **Computational perspective**: Library to compute the systolic ratio of convex polytopes in 4D. It reproduces prior algorithms/results and adds our new algorithm. Layers: (1) thesis writeup; (2) Lean4 formalization of theorems and algorithms; (3) Rust implementation for high-throughput runs over many polytopes; (4) Python interface exposing the same functionality to data scientists and researchers.
- **Data-science perspective**: Pipeline graph of experiments that apply standard data-science methods to investigate when Viterbo's conjecture holds or fails. The math library is treated as a black box producing datasets. Python is the primary environment.
- **Mathematical perspective**: Interpretation of experimental results in their mathematical context. Goals: state new formal conjectures, gain confidence via soft predictions, or prove statements (natural-language proofs, Lean4 proofs, or computational certificates).

## Guiding Principles
- **Complete and explicit records**: Every artifact lives in the git repo; external implicit knowledge is minimized.
- **Meta-documentation**: We also document how the project is developed (workflows, scripts, preparation steps) to keep the repo reproducible and reviewable.
- **Reproducible results**: Every result can be regenerated from the writeup and code in the repo.
- **Fast internal cycle**: No stable API; each commit documents only itself; breaking changes incur no communication overhead.
- **AI agents first-class**: AI agents and Jörn co-develop. Tools, APIs, and docs are written for both. Agents are onboarded to the latest commit; legacy history is not required knowledge.
- **Published**: No external contributors are expected, but the repository is public for reuse.

## Roadmap
See `docs/draft/roadmap.md` for dated milestones and task breakdown.
