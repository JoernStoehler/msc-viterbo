# Roadmap — MSc Viterbo (Dec 2025)

This roadmap is the in-repo source of truth for planning. GitHub issues mirror actionable chunks; update both when plans change.

## Horizon (next 4 months to thesis submission)
- Deliver a reproducible computational study of Viterbo’s conjecture on convex polytopes in \(\mathbb{R}^4\), with code, datasets, and thesis write-up shipped together.
- Primary outcomes: (a) validated capacity-computation and polytope sampling pipeline; (b) catalog of data science experiments and counterexamples to our own hypotheses and investigative methodology; (c) complete thesis PDF and HTML; (d) the Rust library in a clean, trusted, professional state and the Python experiments in a hacky, sanity-checked, extensible state.

## Workstreams and Status

### A. Thesis Write-up (LaTeX)
- Core preliminary math: 
  - [done] symplectic geometry on polytopes. viterbo conjecture.
  - [todo] CZ index and rotation. combinatorial definition.
  - [todo] detailed combinatorial discussion and types we need for CH2021 and our own algorithm.
  - [todo] algorithms from HK2017, CH2021.
  - [todo] HK2024 counterexample discussion.
- [todo] our own algorithm: idea, comparison to HK2017,CH2021, pseudocode, proofs of correctness, theoretical compute and memory analysis.
- [todo] explain the implementation approach (not the code, that's out-of-scope for the thesis and not interesting to mathematicians) of our algorithm (Rust, ai agents for coding, software engineering best practices). document the results: correctness, numerical errors, empirical confirmation of regions of instability, benchmarks, profiling, ablation studies of our algorithm components, stress tests wrt what our algorithm can and cannot do.
- [todo] experiments: philosophy (reproducibility, data-driven, sanity checks, standard data science and machine learning toolbox, ai agents automate the coding so experiments are way, way cheaper than ever before, so we just treat data science as a box of hammers and our hypotheses as nails and hit everything with everything until we get results), long table of experiments we ran and their takeaways including inconclusive ones, then detailed write-ups of the most interesting experiments, defer less refined write ups of less interesting or redundant experiments to the appendix OR even to the code repository as colocated README.md files in the experiment source folders. Lots of figures and tables. Highly optimized for skimming and browsing.
- [todo] hypotheses: write up the hypotheses we formed during our work, as a big table, and what our final believes at the end of the thesis are, with references to the experiments that support or refute them. Detailed write ups again for the interesting non-redundant ones, less detailed for the rest; since we don't have code, everything goes into the chapter here / the appendix for stating with higher detail and precision and verbosity than we want to do in the main text.
- [todo] conclusion: summarize what we did, and the results on the levels of
  - methodology (ai agents for automation of master thesis work, potential and limitations of data science for math, dumb hammers and nails approach, high performance algorithm development)
  - reusable deliverables for future work by other people (reproducible repository, detailed writeup, rust library, python scripts, datasets)
  - mathematical insights, including proofs, conjectures, counterexamples, formalization efforts, new questions raised.
  - assessment of future directions of inquiry (both mathematical and methodological)

### B. Capacity Algorithm (Rust core + FFI)
- [done] Toolchain works, including unit tests, benchmarks, builds, PyO3+maturin; `geom`, `algorithm`, `ffi` crates with placeholder functions.
- [todo] Concrete implementation of 
  - [todo] HK2017 algorithm
  - [todo] CH2021 algorithm
  - [todo] Our own algorithm
  - [todo] Types to express statements about symplectic geometry on polytopes, e.g. a polytope type, a 2-face type, ...; helper functions; formalization as code of various lemmas (e.g. as docstring contract specification with reference to the proof in the thesis, or as unsafe type casts / control flow assertions based on the lemmas).
  - [todo] Pseudorandom sampling and enumeration from interesting polytope families.
  - [todo] FFI bindings for Python interop.
  - [todo] Unit tests of happy paths, edge cases, error paths, regression tests.
  - [todo] Benchmarks and profiling with semi-automated reports. Instrument our algorithm well enough to be able to run (tree shaked / compiler optimized) ablation studies.
- [todo] Add more features into the Rust library as it becomes revealed where the computational hotspots or development friction points are when running experiments; no concrete feature is anticipated, but we do anticipate unknown unknowns will pop up. Example of what we mean: perhaps a certain kind of transformation of polytopes (random jitter) needs to be implemented in rust for performance when we start training ML models.

### C. Experiments & Assets (Python orchestration)
- [done] Pipeline skeleton: hello-world experiment, plotting helper, lint/tests scaffolding setup and passing. Unit tests and e2e tests. Data and config and pipeline conventions documented in AGENTS.md.
- [todo] Basic experiments:
  - [todo] Create a dataset of random/enumerated polytopes of interest
  - [todo] Populate dataset with capacity computations via Rust FFI
  - [todo] Sanity checks (aka e2e tests) both automated and manual (e.g. plot and table assets).
  - [todo] Basic data analysis: what fraction of polytopes satisfy Viterbo's conjecture?
  - [todo] Any identified convenience helpers (e.g. dataset row types, complex plots we want to and actually can standardize).
  - [todo] Write up experiment results in LaTeX chapter(s).
  - [todo] Visualize the minimum action orbits using a stereographic projection (R^4 -> S^3 -> R^3), perhaps interactive with js.
  - [todo] Inspect our algorithm behavior, e.g. plot the 2-face graph and its node+edge data. plot the (exponentially large) search tree e.g. via sampling random paths through it or via aggregate statistics like node counts, especially the comparison wrt how much e.g. ablation of features changes the search tree structure, including e.g. starting with the final value as cutoff instead of a lax upper bound.
- [todo] Advanced experiments:
  - [todo] Counterexample search: more dense sampling, or sampling guided by data science methods (e.g. fit some basic models (all from the tool box! let's have an experiment that's 20 experiments in disguise :3) to predict where the capacity is high)
  - [todo] Local structure: how does systolic ratio behave near a polytope? local maxima and minima? (-> literature has sth to say e.g. Zoll property, but we can also do numerics); e.g. umap/t-sne of polytopes colored by systolic ratio, requires picking (multiple) good distance metrics module uninteresting symplectomorphisms.
  - [todo] ML models: is the systolic ratio a well-posed prediction problem, is it well-behaved and if not, can we say why? (spontaneous first thoughts: too little data, too sparse signal for interesting features, requires too complex algorithms even for approximation and so the models do not learn well, requires special input preparation to avoid weird basins (e.g. a model learning only one PCA component and then getting stuck). Anything interpretable to say if we succeed in teaching a predictive model? Standard toolbox techniques (brainstormed): linear models, decision trees/forests, NNs, input formalization, rich input information (e.g. precomputed features), data multiplication (symplectomorphisms, scaling, continuity under noise, omitting unimportant facets), local derivative information (differentiable second pass of a capacity calculation / perturbation theory), shapley values / feature ablations, training on incomplete data (e.g. input subsets especially for rich input features), iterative refinement (loop architecture, tree search architecture, ...), ensemble methods, curriculum learning (though this is often more about compute efficiency), rich output signal (capacity, volume, systolic ratio, Reeb orbits, spectrum, derivatives, orbit period, ...) for richer feedback, classification (match n systolic ratios with n polytopes) instead of regression, ...
  - [todo] RL ML models: similar, but also works for unknown solutions (e.g. maximize systolic ratio over some polytope space, find a symplectomorphism that maps two polytopes, ...)
- [todo] Asset generation:
  - [todo] Dataset statistics tables
  - [todo] Visualize 4d polytopes (e.g.: projections, graphs, tables, trying to rotate into a nicer view, classify by combinatorial type, ...)
  - [todo] Feature vs feature plots
  - [todo] Similarity plots (e.g. umap/t-sne)
  - [todo] Model training curves, model evaluation plots; this is less interesting for mathematicians, but important for appendix discussions and reproducibility.
  - [todo] Benchmark, profiling reports, ablation study reports.
  - [todo] Graphs of polytopes, graphs of search algorithm behavior, also under ablated versions.
  - [todo] Interactive visualizations (e.g. 3d stereographic projections of polytopes and orbits) hosted on GitHub Pages.
- [todo] Toolchain and scaffolding:
  - [todo] Maintain adherence to best practices, update best practices as we learn more.
  - [todo] Refactor experiment code to stay reproducible, e.g. ignore DRY, keep things explicit and non-magical and isolated, only refactor code to shared helpers once stable and reused multiple times.
  - [todo] Maintain data provisioning: all data and models reproducible, rich meta information is retained just in case for costly data to avoid unnecessary regens (especially trained ML models). Proper PRNG seeding and code versioning (git commit hashes in experiment metadata when experiments are costly to run). Git LFS.
  - [todo] Experiment documentation: update latex_viterbo/ writeup to maintain somewhat live view of all experiments, update local README.md files for info not yet in latex or not suitable for thesis (e.g. bc about low-level code and config and devops and not mathematical insight).
  - [todo] Track pipeline dependencies and data lineage to avoid accidental loss of reproducibility.
  - [todo] Unit test Rust FFI, unit test experiment code only when we don't trust the e2e tests to cover enough ground, use sanity e2e tests that e.g. verify dataset health after pipeline stages, use extra test configs for faster feedback cycles while developing and while testing.
- [todo] Meta:
  - [todo] more hammers, more nails, as we go.

### D. Tooling / DevOps / Coordination
- [done] Devcontainer, shared caches, GitHub Pages build for LaTeX, issue/PR templates, worktree scripts.
  - [todo] GitHub Actions CI for LaTeX is broken right now.
- [todo] Document in onboarding files: no GitHub Actions CI for Rust and Python due to their computational cost; instead rely on targeted local CI runs before submitting PRs.
- [todo] Finish writing a good ROADMAP.md and mention it in root AGENTS.md

## Scheduled Milestones
- [todo] For 2025-12-11: Jörn completes ROADMAP.md
- [todo] For 2025-12-11: Jörn completes our algorithm spec `packages/rust_viterbo/agent_docs/algorithm-spec.md`
- [todo] For 2025-12-11: Jörn finishes the latex chapters on
  - [todo] preliminary math `math.tex`, with a more detailed discussion of Reeb dynamics on polytopes down to the level we need for our algorithm, with a discussion of CZ index and rotation in smooth and polytope setting incl undefined cases.
  - [todo] our and literature algorithms `algorithms.tex`
  - [todo] HK2017 proof appendix `hk2017-appendix.tex`
- [todo] Fpr 2025-12-11: Jörn schedules new milestones, mainly ones that can be delgated to agents.
  - brainstormed ideas: implement symplectic geometry types and functions in Rust, implement algorithms in Rust, implement FFI bindings, implement basic polytope known cases, implement basic polytope families for sampling and enumeration, implement the main Python dataset generation experiment, implement sanity e2e tests for dataset, implement unit tests for FFI in Python, implement benchmarks and profiling and instrumentation and ablation for Rust, write report on benchmark+profiling+instrumentation+ablation results, write report on dataset statistics, automate generation of assets for the reports, write up reports in latex, design and implement visualization experiments for polytopes and orbits and datasets, ...

---
Please keep this file updated when milestones shift; mirror actionable items into GitHub issues for agent pickup.
The roadmap should always be edited in consultation with the project owner (Jörn) since any errors in this document will be highly costly to fix, since agents rely on ROADMAP.md's literal correctness and unambiguity.

_Last updated: 2025-12-11T12:40:00Z by Jörn_
_Last vetted: 2025-12-11T12:40:00Z by Jörn_