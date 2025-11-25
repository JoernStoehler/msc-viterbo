# Roadmap

This roadmap is literal and unambiguous. It is the single source of truth for dated milestones and task intent; do not assume unstated work exists or is implied.

## Completed anchors
- **2025-10-01** — Start of work on the thesis project.
- **2025-10-10** — Switch from the initial feasibility prototype to the current repository.

## Current milestone (2025-11-24) — in progress
- **Writeups**: overview + roadmap exist. `02-geometry.mdx` and `01-algorithm.mdx` still miss: floating-point implementation, CZ/rotation for Lagrangian faces, completed proof appendices, unified notation across text/Lean/Rust.
- **Library**: Lean/Rust/Python scaffolds exist; Rust only has `SymplecticVector` + `oriented_area`. Goal: ship Rust core that computes $c_{EHZ}$ / minimal action for 4D polytopes (H-rep input), returns capacity + one closed characteristic (face sequence + action), and expose via maturin to Python. Lean names/types should mirror where feasible.
- **Quality**: only smoke tests (Rust symplectic form; Python dummy helpers). Add unit/property tests on simple shapes (ball/box/simplex), binding round-trips, Rust–Python parity checks; extend Lean proofs once definitions settle.
- **Pipelines**: only dummy plot pipeline exists. Build real dataset pipeline: JSON configs under `packages/python_viterbo/data/configs/`; outputs in `packages/python_viterbo/data/<dataset>/` with provenance (run params, git commit, seed); figures in `packages/thesis/src/assets/figures/<dataset>/`. Document I/O schemas and reproducibility knobs; wire into tests.
- **Results**: no compiled list of $\text{sys}(K) > 1$ yet. After pipeline runs, verify candidates with the Rust core and publish data + figures + commands.
- **Meta**: setup scripts exist (`scripts/worktree-prepare.sh`, package-local prepares) but runbooks are incomplete. Add a bootstrap checklist (scripts, env vars, caches, data paths, figure build order) for reproducibility.

## Next milestone (2025-11-30) — task breakdown

### Visualization
- Define the stereographic-projection mapping from $\mathbb{R}^4$ polytopes to $\mathbb{R}^3$ models.
- Render static images of each polytope and its minimum-action generalized closed characteristic.
- Ship an interactive 3D viewer in JavaScript; bundle via Astro into the docs site.

### Dataset growth
- Increase sample count across existing polytope families and random draws; track generation parameters.
- Catalog additional cases with $\text{sys}(K) > 1$ and attach evidence (data + plots).
- Version the dataset; document schema and column meanings for reuse.

### Geometric analysis
- Define and implement a metric on convex polytopes modulo (mainly affine) symplectomorphisms.
- Use invariants (volume, capacity, systolic ratio) plus the metric to separate inequivalent cases for clustering and dimensionality reduction.
- Provide a callable API (Rust + Python) to compute distances and invariants for a set of polytopes.

### Data mining and ML
- Run clustering, dimensionality reduction, and PCA on the production dataset; log observed structures.
- Build an ML evaluation harness that ingests multiple encodings (half-spaces, vertices, $h_K(u)$ grid, ...).
- Train and assess models that predict the systolic ratio of a single polytope; accept only models that generalize out of sample; otherwise record failure modes and likely causes.

### Computational checks of known claims
- Reproduce Heim–Kisliv result: no simplex with $\text{sys}(K) > \tfrac{3}{4}$ using a finite cover of the simplex parameter space; attempt extension to six-half-space polytopes.
- Validate Mahler's conjecture in 2D computationally: $\text{sys}(K \times K^\circ) \leq 1$ for convex point-symmetric bodies $K \subset \mathbb{R}^2$; treat as a pipeline regression test.

### Algorithm implementations from literature
- Implement Heim–Kisliv 2019 linear-programming algorithm and expose via Rust + Python.
- Implement Chadez–Hutchings 2021 algorithm (baseline) and expose via Rust + Python.
- Implement Minkowski billiard algorithm (Heim–Kisliv 2024) for Lagrangian products and expose via Rust + Python.
- Add parity tests comparing literature algorithms with our algorithm on shared benchmark cases.

### Performance and robustness
- Benchmark the Rust implementation; profile hotspots; ablate individual optimizations; record CPU time and search-behavior metrics (nodes explored, best candidate over time, pruning frequency).
- Harden against numerical rounding errors with stress tests and fallback strategies. <!-- Specify preferred techniques (interval arithmetic, higher precision, exact subroutines) and acceptable performance cost. -->

### Meta and prerequisites
- Finish the full writeup of our custom algorithm across text, Lean4, and Rust with consistent notation.
- Import the reading list from `/workspaces/worktrees/shared/rust-viterbo/` and link it from this repo's docs.
- Keep runbooks/workflows current so new agents can reproduce pipelines end-to-end.
- Ensure all referenced functionality (projection, metric API, ML harness, parity tests) is documented and discoverable from the docs site.
