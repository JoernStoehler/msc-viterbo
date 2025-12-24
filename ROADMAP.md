# Roadmap

This roadmap is the in-repo source of truth for planning. GitHub issues mirror actionable chunks; update both when plans change.

## Horizon (next 4 months to thesis submission)
- Deliver a reproducible computational study of Viterbo’s conjecture on convex polytopes in \(\mathbb{R}^4\), with code, datasets, and thesis write-up shipped together.
- Primary outcomes: (a) validated capacity-computation and polytope sampling pipeline; (b) catalog of data science experiments and counterexamples to our own hypotheses and investigative methodology; (c) complete thesis PDF and HTML; (d) Rust library in a clean, trusted state and Python experiments in a hacky-but-checked, extensible state.

## Locked constraints (owner-approved, 2025-12-22)
- Research scope: \(\mathbb{R}^4\) only (toy tests in lower dimensions are ok).
- Lean: out of scope permanently.
- Replication target: HK&O via **our tube-based** algorithm; main goal is correctness of the produced value/orbit.
- Lagrangian polytopes (MVP): if \(K\) has any Lagrangian 2-faces, perturb one or both adjacent facet normals (heights fixed) before running the tube algorithm.
- Rotation pruning (MVP): use CH2021 combinatorial rotation number in **turns** (1 = \(2\pi\)); keep \(\rho_{\mathrm{comb}} \le 2\), discard only if \(\rho_{\mathrm{comb}} > 2 + \varepsilon_{\mathrm{rot}}\) to avoid numerical errors.

## Explicitly deferred decisions (track so we don’t forget)
- Perturbation scheme details: concrete epsilon schedule (single epsilon vs sweep + stability check).
- Numerical tolerances: concrete `eps_lagr` and geometry tolerances beyond “calibrate after first runs”.
- Dataset size + compute budgets: to be discussed later with the owner; current rough guess is “~1 min for tests, up to ~24h for big runs” (not locked).
- “Distance metric” / landscape analysis: to be developed later (owner has ideas; not committed yet).
- Replication/unit-test tolerances: calibrate once the first implementation runs (“we’ll know when we see it”).

## Workstreams and Status

### A. Thesis Write-up (LaTeX)
- Core preliminary math (partial):
  - [done] symplectic geometry on polytopes; Viterbo conjecture statement.
  - [todo] CZ index and rotation; combinatorial definition; CH2021 combinatorial types needed for the algorithm.
  - [todo] exposition of HK2017 and CH2021 algorithms (math-side only).
- [todo] HK2024 counterexample discussion (in the counterexample chapter, not prelims).
- [todo] Our algorithm chapter: idea, comparison to HK2017/CH2021, pseudocode, correctness, complexity.
- [todo] Implementation approach and results (Rust, agents, SE practices); correctness, numerical errors, instability regions, benchmarks, profiling, ablations, stress tests.
- [todo] Experiments chapter: philosophy, table of experiments (incl. inconclusive), detailed write-ups for key runs; others to appendix or per-experiment READMEs; heavy on figures/tables for skimming.
- [todo] Hypotheses table with final beliefs and links to supporting/refuting experiments; detailed write-ups for non-redundant ones.
- [todo] Conclusion: methodology takeaways; reusable deliverables; mathematical insights/proofs/conjectures/formalization; future directions.

### B. Capacity Algorithm (Rust core + FFI)
- [partial] Toolchain builds; unit tests; PyO3/maturin bindings; crates `geom`, `algorithm`, `ffi` have placeholders. Benchmarks/profiling still TODO.
- Dependency: implement the tube algorithm only after the algorithm contract is owner-approved (see `packages/rust_viterbo/agent_docs/algorithm-spec.md`).
- [todo] Owner-approved algorithm contract for the tube algorithm (including rotation pruning + perturb-if-Lagrangian policy).
- [todo] Concrete implementation of the tube algorithm (branch-and-bound + pruning + witness orbit output).
- [todo] (Deferred) Decide whether implementing HK2017 / CH2021 algorithms in Rust adds enough validation value to justify the cost.
- [todo] Types for polytopes, 2-faces, helpers; encode lemmas/contracts alongside code.
- [todo] Pseudorandom sampling/enumeration of polytope families.
- [todo] FFI bindings for Python interop.
- [todo] Tests: happy-path, edge/error cases, regression.
- [todo] Benchmarks/profiling with semi-automated reports; instrumentation for ablations.
- [todo] Emergent features to reduce hotspots/friction as experiments scale (e.g., fast jitter transforms if needed).

### C. Experiments & Assets (Python orchestration)
- [done] Pipeline skeleton: hello-world experiment, plotting helper, lint/tests scaffolding passing; conventions in AGENTS.md; HK&O counterexample generator exists, other datasets pending.
- [todo] Basic experiments:
  - [todo] Create a dataset of random/enumerated polytopes of interest.
  - [todo] Populate dataset with capacity computations via Rust FFI.
  - [todo] Sanity checks (aka e2e tests) both automated and manual (e.g. plot and table assets).
  - [todo] Basic data analysis: what fraction of polytopes satisfy Viterbo's conjecture?
  - [todo] Any identified convenience helpers (e.g. dataset row types, complex plots we want to and actually can standardize).
  - [todo] Write up experiment results in LaTeX chapter(s).
  - [todo] Visualize the minimum action orbits using a stereographic projection (R^4 -> S^3 -> R^3), perhaps interactive with JS.
  - [todo] Inspect our algorithm behavior, e.g. plot the 2-face graph and its node+edge data; plot the (exponentially large) search tree e.g. via sampling random paths through it or via aggregate statistics like node counts, especially the comparison wrt how much e.g. ablation of features changes the search tree structure, including e.g. starting with the final value as cutoff instead of a lax upper bound.
- [todo] Advanced experiments:
  - [todo] Counterexample search: more dense sampling, or sampling guided by data science methods (e.g. fit some basic models (all from the tool box; let's have an experiment that's 20 experiments in disguise) to predict where the capacity is high).
  - [todo] Local structure: how does systolic ratio behave near a polytope? local maxima and minima? (literature has something to say, e.g. Zoll property, but we can also do numerics); e.g. UMAP/t‑SNE of polytopes colored by systolic ratio, requires picking (multiple) good distance metrics modulo uninteresting symplectomorphisms.
  - [todo] ML models: is the systolic ratio a well-posed prediction problem, is it well-behaved and if not, can we say why? (spontaneous first thoughts: too little data, too sparse signal for interesting features, requires too complex algorithms even for approximation and so the models do not learn well, requires special input preparation to avoid weird basins (e.g. a model learning only one PCA component and then getting stuck). Anything interpretable to say if we succeed in teaching a predictive model? Standard toolbox techniques (brainstormed): linear models, decision trees/forests, NNs, input formalization, rich input information (e.g. precomputed features), data multiplication (symplectomorphisms, scaling, continuity under noise, omitting unimportant facets), local derivative information (differentiable second pass of a capacity calculation / perturbation theory), Shapley values / feature ablations, training on incomplete data (e.g. input subsets especially for rich input features), iterative refinement (loop architecture, tree search architecture, ...), ensemble methods, curriculum learning (often more about compute efficiency), rich output signal (capacity, volume, systolic ratio, Reeb orbits, spectrum, derivatives, orbit period, ...) for richer feedback, classification (match n systolic ratios with n polytopes) instead of regression, ...
  - [todo] RL ML models: similar, but also works for unknown solutions (e.g. maximize systolic ratio over some polytope space, find a symplectomorphism that maps two polytopes, ...).
- [todo] Assets:
  - [todo] Dataset statistics tables.
  - [todo] Visualize 4d polytopes (e.g.: projections, graphs, tables, trying to rotate into a nicer view, classify by combinatorial type, ...).
  - [todo] Feature vs feature plots.
  - [todo] Similarity plots (e.g. UMAP/t‑SNE).
  - [todo] Model training curves, model evaluation plots (less interesting for mathematicians, but important for appendix discussions and reproducibility).
  - [todo] Benchmark, profiling reports, ablation study reports.
  - [todo] Graphs of polytopes, graphs of search algorithm behavior, also under ablated versions.
  - [todo] Interactive visualizations (e.g. 3d stereographic projections of polytopes and orbits) hosted on GitHub Pages.
- [todo] Tooling/scaffolding:
  - [todo] Maintain adherence to best practices, update best practices as we learn more.
  - [todo] Refactor experiment code to stay reproducible, e.g. ignore DRY, keep things explicit and non‑magical and isolated, only refactor code to shared helpers once stable and reused multiple times.
  - [todo] Maintain data provisioning: all data and models reproducible; rich meta information retained for costly data to avoid unnecessary regens (especially trained ML models). Proper PRNG seeding and code versioning (git commit hashes in experiment metadata when experiments are costly to run). Git LFS.
  - [todo] Experiment documentation: update latex_viterbo write‑up to maintain somewhat live view of all experiments; update local README.md files for info not yet in LaTeX or not suitable for thesis (e.g. low‑level code/config/devops rather than mathematical insight).
  - [todo] Track pipeline dependencies and data lineage to avoid accidental loss of reproducibility.
  - [todo] Unit test Rust FFI; unit test experiment code only when we don't trust the e2e tests to cover enough ground; use sanity e2e tests that e.g. verify dataset health after pipeline stages; use extra test configs for faster feedback cycles while developing and while testing.
- [todo] Meta:
  - [todo] more hammers, more nails, as we go.

### D. Tooling / DevOps / Coordination
- [done] Devcontainer, shared caches, GitHub Pages build for LaTeX, issue/PR templates, worktree scripts.
  - [todo] Verify LaTeX CI status; issue #16 may be stale (update/close once verified).
- [todo] Onboarding note: Rust/Python GitHub Actions CI intentionally absent; run local lint/test before PRs.
- [todo] Keep ROADMAP.md current and referenced from root AGENTS.md.
- [todo] Conventions (coords (q1,q2,p1,p2), \(J(q,p)=(-p,q)\), assets under `packages/latex_viterbo/assets/`) are defined in AGENTS; keep code/docs consistent.

## Scheduled Milestones
- [todo] Target finish: 2026-03-14 (soft target).
- [todo] Hard end: 2026-04-14.
- [todo] Printing/shipping buffer: ~1 week.
- [todo] Replace deprecated 2025-12-11 “soft target” milestones with a current milestone breakdown (owner + PM).

---
Please keep this file updated when milestones shift; mirror actionable items into GitHub issues for agent pickup. The roadmap should always be edited under tight interaction with the project owner (Jörn); agents rely on its literal correctness.

_Last updated: 2025-12-22. Review (Jörn): pending_
