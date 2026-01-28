# TODO

[proposed]

Consolidated task tracking for the thesis project. Migrated from GitHub Issues and experiments.md on 2026-01-27.

**Structure:**
- Checklist sections at top for quick scanning
- Detailed sections at bottom for items needing context
- Status: `[ ]` pending, `[x]` done, `[-]` blocked/deferred

See `.claude/skills/project-management/SKILL.md` for conventions.

---

## Algorithm Toolbox

**CRITICAL (blocks experiments):**
- [ ] Debug triangle×triangle discrepancy: billiard=3.0 vs hk2017=1.5 (investigate which is correct)
  - Add orbit validation tests to billiard (port from tube/tests/orbit_invariants.rs)
  - Verify returned orbits are valid Reeb orbits (breakpoints on facets, segments along Reeb vector)
  - Trace mathematical reason for discrepancy, not just pattern matching

**Algorithm completion:**
- [x] Polytope faces: 2-face extraction + adjacency + transition maps (#28) (2026-01-28, part of tube implementation)
- [x] Tube algorithm core: branch-and-bound + robust pruning + witness (#29) (2026-01-28, 69 tests passing)
- [x] Volume(K) in R⁴ + systolic ratio + baseline tests (#31) (2026-01-28, QHull integration via PR#90)
- [x] Refactor polytope_database into modular stages (2026-01-28, PR#89):
  - stage_polytopes.py: generate polytope geometries (tesseract, simplex, cross-polytope, 24-cell, random)
  - stage_volume.py: uses ffi.volume_hrep() for real volume calculations
  - stage_capacity.py: uses ffi.tube_capacity_hrep() and ffi.hk2017_capacity_hrep() for real capacities
  - All tests passing (37 tests); SPEC.md updated; stage_build.py deprecated
  - CI consolidated to 2 jobs: Rust + FFI (Rust+Python)
- [~] Cross-algorithm validation (algorithm-comparison experiment): billiard vs hk2017 on Lagrangian products — IN PROGRESS
  - [x] FFI: exposed billiard and tube algorithms
  - [x] stage_build.py: runs billiard + HK2017 on Lagrangian products
  - [x] Documented known triangle×triangle discrepancy (billiard=3.0, hk2017=1.5)
  - [ ] Expose fixtures via FFI (cross-polytope, 24-cell, asymmetric, random_hrep)
  - [ ] Run HK2017 vs Tube comparison on non-Lagrangian polytopes
  - [ ] stage_analyze.py: compute agreement metrics, error tables
  - [ ] stage_plot.py: visualize capacity comparisons, timing analysis

**Lower priority:**
- [ ] Benchmarks/profiling harness for algorithm trusted v1 (#33)
- [-] Download HK thesis: verify sys ≤ 3/4 for simplices claim, extract known polytope values for validation — blocked on CC web (no CONNECT tunneling for JS pages); retry in local devcontainer
- [x] FFI cleanup: removed archived stubs, legacy aliases, fixed type stubs (#37) (2026-01-27)
- [-] HK2017 QCQP solver: remove interior-point assumption — blocked on higher-prio items; big feature but worth background attempt

## Thesis Writing

- [x] Talk: Clarke duality — migrate text content to thesis (2026-01-27)
- [ ] Add images to Clarke duality talk (#41, manual) — see `\DraftImage` placeholders in `packages/latex_talk_clarke_duality/main.tex`

## Research Experiments

**Blocked on volume computation (#31):**
- [-] billiard-hko-orbit — needs systolic ratio (volume + capacity)
- [-] random-polytope-sys-distribution — needs systolic ratio
- [-] lagrangian-product-polygons — needs systolic ratio
- [-] lagrangian-product-random-polygons — needs systolic ratio
- [-] fixed-facet-vertex-count — needs main dataset with systolic ratios
- [-] dataset-dimension-reduction — needs main dataset with systolic ratios
- [-] sys-ratio-optimization — needs systolic ratio

**Blocked on other dependencies:**
- [-] algorithm-performance-comparison — needs all algorithms validated (triangle×triangle bug)
- [-] algorithm-optimization-ablation — blocked: performance comparison first

**Blocked on other dependencies (continued):**
- [-] nn-regression-mutual-info — blocked: main dataset
- [-] ml-capacity-prediction — blocked: large labeled dataset

**Completed:**
- [x] 4d-polytope-visualization — executed 2026-01-27
- [x] benchmark-hk2017 — executed 2026-01-26

## Mysteries to Investigate

- [x] Session-start hook printing output unexpectedly: hook was configured to be silent, but `SessionStart:startup hook success: [repo-map]` appeared in agent context. Why?
  - **Fixed (2026-01-28):** Removed `repo-map.sh` call from session-start hook. Hook now only installs gh CLI (silent). Converted `repo-map.sh` → `repo-map.py` (pure Python) for manual use.
- [ ] Skills not auto-loading in CC web: skill descriptions should auto-inject per https://code.claude.com/docs/en/skills but don't. Workaround: manual skill index in CLAUDE.md. Remove workaround when CC fixes this.
  - **NOT the cause:** permissions.allow list (disproven - WebFetch/Edit worked fine despite not being listed)
  - **Fixed:** `rust-testing/SKILL.md` missing frontmatter
  - **Likely cause:** Known Claude Code bugs that silently abort skill loading:
    - #20576: ENOENT on managed skills directory aborts all loading
    - #17078: False-positive inode deduplication skips skills
    - #12527: macOS quarantine attributes
  - **Also changed:** Simplified settings.json to deny-only (unrelated to skills, but cleaner config)
  - **Verification needed:** Test in new session to see if skills load after frontmatter fix

## Code Quality <!-- unapproved -->

Tasks identified during code quality assessment (2026-01-27).

**Parallelizable:**
- [ ] Move math content to thesis: audit code comments and specs for proofs/definitions that should live in thesis, then migrate them (thesis becomes authoritative source, code/specs reference it)
- [x] Add CI workflows for Rust and Python (low effort, safety net) (2026-01-27)
- [ ] Optimize CI time when test suite grows (parallel pytest, cargo caching, test splitting)
- [ ] Profile CI performance after PR#90: CI time increased to >2min (borderline acceptable). Investigate what's slow (QHull compilation? volume tests?) and whether speedups are possible without reducing test coverage
- [ ] Clean up dead smoke-test.sh (references non-existent tests/smoke/)

**Bottleneck (do serially):**
- [ ] Build out geom as a proper library crate for symplectic + euclidean geometry in 2D and 4D. Goal: clean reference implementations that algorithms build upon. Algorithms can still use custom types when needed — duplication is fine when purposeful. Having clean geom code makes deviations obvious and intentional. Include: symplectic form, J matrix, reeb vector, Sp(2) rotations, 2D polygon primitives. See exploration agent a7a3362 for detailed inventory of what's currently duplicated where.

**Done:**
- [x] Achieve clean tool output (pyright 0 errors/warnings, ruff clean, clippy 0 warnings) (2026-01-27)
- [x] Document "no coverage tools" decision in quality-improvement skill (2026-01-27)
- [x] Fix codespace devcontainer build: use pre-built features instead of manual installs, remove TexLive (2026-01-28)

## Deferred Decisions (#24)

- Perturbation scheme details
- Numerical tolerances
- Dataset size + compute budgets
- Distance metric / landscape analysis
- Replication/unit-test tolerances

## Done

- [x] benchmark-hk2017 (2026-01-26) — see details below
- [x] talk-migration: Clarke duality text content migrated to chapter 08 (2026-01-27)
- [x] 4d-polytope-visualization (2026-01-27) — see details below

---

# Details

Items needing more context than a one-liner. Not every item needs a section here.

## billiard-hko-orbit

**Purpose:** Validation experiment. HK2024 provides ground truth, so discrepancies indicate algorithm bugs.

**Ground truth (HK2024 + thesis data):**
- Systolic ratio: exactly (√5+3)/5 ≈ 1.0472135955
- Capacity: 2cos(π/10)(1+cos(π/5)) ≈ 3.4410
- Orbit type: "2-bounce" — 2 bounces per projection (q and p), so ~4 segments total

**Orbit structure:**
- Polytope is P₅ ×_L R(-90°) P₅ (Lagrangian product of pentagons)
- Each segment: one component (q or p) moves along polygon boundary, other is constant
- Alternates: q-move → p-move → q-move → p-move
- Visualization: side-by-side projections onto q-plane and p-plane, labeled segment numbers
- Infinite family of minimum-action orbits exists; we plot whichever the algorithm returns

**Success criteria:**
- Systolic ratio within 0.1% of ground truth
- Orbit visualization shows 2-bounce pattern in each projection
- Visual inspection confirms orbit shape

## random-polytope-sys-distribution

**Research question:** How rare are counterexamples to Viterbo's conjecture?

**Approach:** Generate "natural looking" random polytope families that are computationally tractable (facet count ≤ 16 should be small enough), compute systolic ratio for ~1k samples, and observe how often sys > 1.

**Polytope families to compare:**
- Convex hull of random points in R⁴
- Intersection of random halfplanes in R⁴
- These may behave differently as random variables over sys

**Analysis:**
- Histogram of sys values (merged families and split by family)
- Fraction of rows with sys > 1
- Check if HKO 2024 counterexample (sys ≈ 1.047) is "special" — is it extremal, or do higher systolic ratios appear in random sampling?

**Strategic implications:**
- If sys > 1 is rare: we need targeted search methods to find interesting polytopes (connects to `sys-ratio-optimization`)
- If sys > 1 is common: random sampling provides enough interesting data already

## lagrangian-product-polygons

**Research question:** What patterns emerge in systolic ratio for Lagrangian products of regular polygons?

**Family parameterization:** (k, m, φ) where:
- k = vertex count of first polygon (regular k-gon)
- m = vertex count of second polygon (regular m-gon)
- φ ∈ [0, 2π/m) = rotation angle applied to second factor

The rotation range is WLOG due to:
1. Symplectomorphism invariance of capacity
2. Symmetry group of the m-gon

**Sampling strategy:**
- Systematic: all (k, m) pairs up to some cutoff
- Random angles within [0, 2π/m)
- "Fractional" angles (e.g., π/12, π/6, ...) for interpretable special cases
- Cutoffs and sample counts determined by computational budget and early insights into value-of-information tradeoffs

**Questions to investigate:**
- Is there a global maximum of sys in this family? What is it?
- Are there monotonic sequences (e.g., sys increasing with k for fixed m, φ)?
- How does the fraction of sys > 1 behave as we vary k, m, φ?
- Is there an optimal angle φ_opt(k, m) that maximizes sys? Can we find an explicit or implicit formula?

**Analysis approach:** Exploratory — generate many independent analysis stages/functions/plots. We don't know what patterns will emerge.

## lagrangian-product-random-polygons

**Research question:** What patterns emerge for Lagrangian products of random 2D polygons?

**Motivation:** Regular polygons are a thin slice of polygon space. Random polygons might reveal different phenomena.

**Random polygon generation methods:**
- Convex hull of random points in R² (various distributions: uniform in disk, uniform in square, Gaussian, ...)
- Random sampling with symmetry constraints:
  - Central symmetry (P = -P)
  - Rotational symmetry (k-fold)
  - Mirror symmetry

**Analysis:** Same exploratory approach as `lagrangian-product-polygons` — independent dataset, throw data science toolbox at it (plots, tables, statistics).

**Relationship to other experiments:** Can later merge with main dataset or keep separate for cleaner analysis.

## fixed-facet-vertex-count

**Research question:** What can we say about sys distribution when we fix combinatorial complexity (facet count or vertex count)?

**Prior work (to verify):**
HK's MSc thesis reportedly shows that simplices in 4D (5 vertices ⟺ 5 facets) satisfy:
- sys ≤ 3/4
- Unique global maximum at the orthonormal simplex (up to symplectomorphisms — there are infinitely many maxima related by Sp(4) ⋉ R⁴, but they're all equivalent)

**Note on star-shapedness:** The "unit simplex" = conv{0, e₁, e₂, e₃, e₄} doesn't contain 0 in its interior, but capacity is still well-defined even for non-star-shaped polytopes. We ignore the extra translation needed.

**Verify via "Download HK thesis" task above:**
- Did she prove sys ≤ 3/4 for simplices?
- Is the orthonormal simplex the unique maximum?
- Amend this research question based on what she actually proved

**HK thesis location:**
- TAU library: https://tau.primo.exlibrisgroup.com/permalink/972TAU_INST/quev9q/alma9932955590304146
- Requires JS rendering; use Playwright in local devcontainer or open in browser

**Experiment:** Filter the main random polytope dataset by facet count or vertex count, examine the resulting sys distribution. Can we:
- Empirically confirm HK's result for simplices?
- Make analogous conjectures for other fixed counts (6-facet polytopes, 7-facet, ...)?

## algorithm-performance-comparison

**Research question:** How do Billiard, HK2017, and Tube compare in performance? What are the scaling laws?

**Approach:** Create a smaller dataset with instrumented Rust code, collect benchmark/profile/instrumentation data on random and enumerated polytopes across different families.

**Data to collect:**
- CPU time (= wall time for single-threaded)
- Profiling data (where is time spent?)
- Algorithm-specific counters:
  - Tube: number of tubes considered during branch-and-bound
  - HK2017: number of permutations enumerated

**Questions:**
- How does CPU time scale with input parameters (facet count, vertex count, ...)?
- Which algorithm is fastest for which family?
- Can we see asymptotic scaling laws (O(n!), O(2^n), ...)?

**Constraints:**
- Not all algorithms work on all inputs:
  - Billiard: only Lagrangian products
  - Tube: requires non-Lagrangian 2-faces
  - HK2017: works on all polytopes (universal baseline)
- Can only compare algorithms on families where multiple apply

**Connection to optimization:** Identifies hotspots for `algorithm-optimization-ablation`

## algorithm-optimization-ablation

**Research question:** Which algorithmic components have what performance impact? Can we optimize without breaking correctness?

**Approach:**
1. Keep a trusted reference implementation that we never modify
2. Create optimized variants with components toggled on/off
3. Ablation study: measure performance impact of each component
4. Cross-check against profiling to verify ablation results are consistent with where time is actually spent

**Example ablation:** Tube algorithm's "rotation upper bound"
- With bound: we track rotation at each step and prune branches that can't close
- Without bound: skip rotation tracking (saves CPU per tube) but visit more nodes in the search tree
- Question: what's the net effect? Does the pruning pay for itself?

**Correctness guarantee:** Always assert that optimized variants produce the same capacity as the reference implementation.

## 4d-polytope-visualization

**Research question:** How can we visualize 4D polytopes and Reeb dynamics in 3D (rendered to 2D screen)?

**Projection pipeline:**
1. **Radial projection to S³:** For polytope K star-shaped w.r.t. 0, map v ∈ ∂K to v/|v| ∈ S³
2. **Stereographic projection S³ → R³:** Standard conformal map (preserves angles, curves straight edges)
3. **3D rendering:** Standard techniques to 2D screen

**What to render:**

*Polytope structure:*
- 3-facets become volumes with piecewise-smooth boundary
- 2-faces → translucent curved surfaces (triangulated mesh or raytraced)
- 1-faces → curved lines
- 0-faces → points

*Reeb dynamics:*
- Reeb trajectories → curved/piecewise-smooth lines with direction arrows (no longer piecewise-linear after projection)
- Tubes → bundles of trajectories rendered as translucent volumetric tubes
- Reeb vector field → explicit arrows or implied by trajectory directions

**Open questions:**
- Best rendering technology (three.js, raytracing, ...)?
- Interactive vs static figures?
- How to handle occlusion and visual clutter?

**Not blocked:** This is primarily a visualization/tooling task, not dependent on algorithm correctness (can use any capacity values, even incorrect ones, for visualization development)

## dataset-dimension-reduction

**Research question:** Can we identify clusters or structures in the polytope dataset via dimension reduction?

**Approach:** Treat the main dataset as a high-dimensional point cloud and apply standard exploratory data analysis:

**Linear methods:**
- Scatter plots of 2-3 numeric columns against each other
- Filter/group by categorical columns (family, facet count, ...)
- PCA to find principal directions of variation

**Nonlinear methods:**
- UMAP for nonlinear dimension reduction
- t-SNE as alternative

**Statistical methods:**
- Regression models to detect mutual information between columns
- Correlation matrices

**Goal:** Find structure that suggests hypotheses — clusters of similar polytopes, continuous manifolds, outliers, relationships between geometric features and sys.

## nn-regression-mutual-info

**Research question:** Can a neural network find non-linear mutual information between polytope features and sys that linear methods miss?

**Motivation:** Extension of `dataset-dimension-reduction`. Linear regression and PCA only capture linear relationships. A neural network can learn arbitrary nonlinear functions.

**Approach:** Train NN as regression model: features → sys. If the NN achieves low loss, there's learnable structure. Analyze what the NN learned (feature importance, hidden representations).

**Relationship to other experiments:**
- Builds on `dataset-dimension-reduction`
- Simpler than `ml-capacity-prediction` (regression on extracted features vs learning capacity from raw polytope)

## ml-capacity-prediction

**Research question:** Can ML learn a scalable (blackbox) capacity algorithm? How learnable is c_EHZ?

**Motivation:** If exact algorithms don't scale to high facet counts, maybe we can learn an approximate predictor that generalizes.

**Knobs to explore:**
- **Dataset:** Size, diversity, which families
- **Architecture:** MLP, GNN (graph of faces), transformer, ...
- **Training objective:**
  - Standard regression loss
  - With noise (for robustness)
  - Iterative/multi-stage (e.g., first autoencoder for symplectomorphism-invariant representation, then capacity predictor)
  - RL setup if we frame it as sequential decision-making
- **Input encoding:**
  - Raw H-rep or V-rep
  - Precomputed nonlinear features (volume, surface area, moments, ...)
  - Redundant representations so the model can latch onto what's useful
- **Architecture size:** How much capacity (model capacity, not symplectic capacity) is needed?

**Using capacity axioms:**
- Symplectomorphism invariance: augment training data with Sp(4) ⋉ R⁴ transformations, or build invariance into architecture
- Scaling: c(λK) = λ²c(K) — can generate infinite training pairs from one polytope
- Monotonicity: K ⊆ L ⟹ c(K) ≤ c(L) — use as regularization or constraint
- Continuity: small perturbations → small changes in capacity

## sys-ratio-optimization

**Research question:** Can we use optimization to find polytopes with maximum systolic ratio? What do the gradient flow lines look like?

**Optimization methods to try:**
- **Rejection sampling:** Generate random polytopes, keep those with higher sys than current best
- **Gradient descent:** If we can compute ∂sys/∂(h-rep) or ∂sys/∂(v-rep), follow the gradient. Requires differentiable capacity computation or finite-difference approximation.
- **RL:** Frame as sequential modification of polytope, reward = sys improvement. Policy could be NN or simpler.

**Gradient flow analysis:**
- Treat sys as a function on the space of polytopes
- Study flow lines of ∇sys
- Characterize critical points: local maxima, global maxima, saddle points
- Literature question: Are there known results on what a convex body must look like to be a local optimum of sys?

**Lie group structure:**
The group Sp(4) ⋉ R⁴ of affine symplectomorphisms acts on polytopes. This action:
- Preserves capacity (by definition of symplectic capacity)
- Preserves volume (symplectomorphisms have det = 1)
- Therefore preserves sys = c²/(2·Vol)

Consequences:
- Lie algebra generators of Sp(4) ⋉ R⁴ act as tangent directions in polytope space
- These directions have ∂sys = 0, so they're orthogonal to ∇sys
- The sys function is constant on orbits of the Lie group action

**Quotient perspective:**
If we quotient polytope space by Sp(4) ⋉ R⁴, we get a lower-dimensional space where:
- Each point represents an equivalence class of symplectomorphic polytopes
- sys is well-defined on the quotient
- Gradient flow on the quotient might be simpler to understand/visualize

## benchmark-hk2017

**Status:** Executed (2026-01-26)

**Research question:** How does HK2017 runtime scale with polytope parameters? Can we build predictive models for runtime?

**Key results:**

| Metric | Value |
|--------|-------|
| Scaling model | `time_ms = 5.51e-04 × perms^1.059` |
| Model fit | R² = 0.9997 |
| Time per permutation | ~1.04 µs |
| Permutation count formula | `Σ_{k=2}^F (F! / (F-k)!)` — exact match to observations |

**Budget guidance:**

| Facets | Permutations | Expected Time |
|--------|--------------|---------------|
| 5 | 320 | ~0.3 ms |
| 8 | 109,592 | ~110 ms |
| 9 | 986,400 | ~1.3 s |
| 10 | 9,864,090 | ~10-13 s |

**Practical rule:** Given time budget T (seconds), max facets F where theoretical perms ≤ T × 10⁶.

**Discoveries:**
1. **Facet count gaps in 4D:** Random convex hulls cannot produce 6, 7, or 10 facets. Only 5 (simplex from 5 points) or 8+ (from 6+ points).
2. **GraphPruned works:** 2-7x faster than Naive, identical results. Recommended for production use.
3. **FFI limit:** 10 facets maximum is enforced by the FFI.

**Files:**
- Experiment module: `packages/python_viterbo/src/viterbo/experiments/benchmark_hk2017/`
- Data: `packages/python_viterbo/data/benchmark-hk2017/`
- Detailed findings: `FINDINGS.md` in experiment module

**Future work:**
- Test larger facet counts by removing FFI limit
- Profile bottlenecks for optimization

---

**Provenance:** Experiments below benchmark-hk2017 were added during a brainstorming session between Jörn and a Claude agent (2026-01-26). Some ideas originated from Jörn's prior discussions with his thesis advisor.
