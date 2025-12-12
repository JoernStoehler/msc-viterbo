# Capacity Algorithm Spec (skeleton, Dec 2025)

This is a working spec for the Rust implementation of the polytope capacity/closed-characteristic algorithm. Owner will revise math details; agents should not fill gaps without confirmation.

## Goal
- Compute/approximate \(c_{\mathrm{EHZ}}(K)\) for an admissible polytope \(K\subset\mathbb{R}^4\) given by outward unit facet normals \(n_i\) and heights \(h_i>0\).
- Produce: capacity value, simple minimizing orbit data (facet order, time weights), and diagnostics suitable for validation/plots.

## Inputs
- Facets: list of \((n_i\in\mathbb{R}^4,\, h_i>0)\) in thesis convention \((q_1,q_2,p_1,p_2)\), \(J(q,p)=(-p,q)\). Normals must be unit length; caller guarantees irredundant H-rep.
- Flags: symmetry (centrally symmetric?), tolerance settings, rotation-number cap if used.
- Optional: precomputed adjacency (facets meeting at 2-faces) to avoid recomputing.

## Outputs
- Capacity estimate/value with error bound or certificate of optimality.
- Simple orbit descriptor: permutation \(\sigma\) of facets used, weights \(\beta_i\ge 0\) (time fractions), and derived velocities \(p_i=(2/h_i)J n_i\).
- Diagnostics: feasibility residuals (closure, constraints), action, rotation number if computed, iteration counts.

## Conventions
- Action \(A(\gamma)=\tfrac12\int\langle J\gamma,\dot\gamma\rangle dt\).
- HK/CH combinatorial formula (non-Lagrangian case): maximize \(Q(\sigma,\beta)=\sum_{j<i}\beta_{\sigma(i)}\beta_{\sigma(j)}\,\omega(n_{\sigma(i)},n_{\sigma(j)})\) under \(\sum \beta_i h_i=1\), \(\sum \beta_i n_i=0\); then \(c_{\mathrm{EHZ}}=\tfrac12 / \max Q\). <!-- source: math/09-hk-ch-formula.tex -->
- Rotation-number pruning (if used): bound \(\rho\le 2\) per CH21 to keep search finite. <!-- source: legacy flow-graph discussion -->

## Planned algorithm (owner to confirm)
- Outer search over admissible facet orders \(\sigma\) (permutation with possible symmetry pruning).
- Inner solver for weights \(\beta\) satisfying linear constraints and maximizing \(Q\) (convex quadratic subject to linear eq + nonnegativity; can be framed as QP or small fixed-point).
- Candidate propagation on 2-faces: maintain candidate points on last visited 2-face; push forward through facet velocities to prune impossible orders early (branch-and-bound on flow graph). <!-- source: legacy flow-graph + pushforward idea in shared notes -->
- Branch-and-bound:
  - Upper bound: relax nonnegativity or drop order constraint to get fast bound.
  - Lower bound: feasible \((\sigma,\beta)\) yields action.
  - Cut if bound >= best found (remember \(c_{\mathrm{EHZ}} = 1/(2 \max Q)\)).
- Degeneracies: handle Lagrangian 2-faces by allowing slide/cone velocities or by perturbation; owner to decide.

## Numerical/solver choices
- Small dimension: prefer analytic/closed-form where possible; otherwise use dense QP (e.g., `nalgebra` + simple projected gradient/active set).
- Tolerances: residuals for \(\sum \beta_i h_i=1\), \(\sum \beta_i n_i=0\); nonnegativity; permutation feasibility.
- Determinism: stable ordering, seeded RNG if needed.
- Solver knobs to decide (owner):
  - QP backend: projected gradient vs. active-set vs. cvxopt equivalent in Rust; target condition numbers.
  - Early exit/branch bound: bound from relaxed QP, cutoff if bound exceeds best action.
  - Handling infeasible permutations: nullspace detection (SVD) vs. fallback to regularization.

## Validation & Tests
- Regression polytopes (to be added under `packages/python_viterbo/data/`):
  - HK&O 2024 counterexample (expected \(c_{\mathrm{EHZ}}\) and systolic ratio > 1).
  - Cube or product-of-intervals (sanity: \(\mathrm{sys}=1\) bound).
  - Non-Lagrangian toy with known ordering (owner to supply).
- Unit tests: verify closure and constraints for known \((\sigma,\beta)\); compare against literature values within tolerance.
- Diagnostics to export for tests: constraint residuals, chosen permutation, \(\beta\) vector, \(Q(\sigma,\beta)\), estimated error bound.

## Open questions for owner
- Exact admissible set for facet orders: all permutations vs. constrained by adjacency/flow graph?
- Treatment of Lagrangian 2-faces: perturb, exclude, or explicit cone handling?
- Required error bounds: certified (e.g., rational arithmetic) vs. floating upper/lower bounds?
- Preferred solver flavor (QP vs. fixed-point) and stopping criteria.

## Handoff to thesis
- Once spec is confirmed, mirror it into LaTeX algorithm chapter; keep this Markdown terse for implementers.
