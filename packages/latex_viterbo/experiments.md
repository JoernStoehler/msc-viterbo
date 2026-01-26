# Experiments Tracking

This is a living document tracking research ideas and experiments for the thesis. It is not a rigid specification.

**Context:** This project studies Viterbo's Conjecture for convex polytopes in R⁴ (4-dimensional real space, the symplectic setting). "4D" throughout means R⁴.

**Structure:**
- The **table** is a quick-scan index — brief entries for scanning
- Each experiment has a **detailed section** below (e.g., `## random-polytope-sys-distribution`) that preserves full reasoning, sub-questions, connections, and context
- Don't compress ideas into minimal table notes; write the detailed section

**Status values:** Ideation | Specified | In progress | Executed | Polished | Abandoned | Failed | Superseded

See `.claude/skills/experiment-workflow/` for the full workflow.

---

**Provenance (2026-01-26):** The experiments below `billiard-hko-orbit` were added during a brainstorming session between Jörn and a Claude agent. Some ideas originated from Jörn's prior discussions with his thesis advisor and notes on paper; these were articulated and refined during the session. The detailed sections attempt to preserve the full reasoning as it was developed.

| Label | Status | Research Question | Notes |
|-------|--------|-------------------|-------|
| billiard-hko-orbit | Ideation (blocked) | Compute EHZ capacity for HK-O 2024 counterexample using billiard algorithm; verify systolic ratio ≈ 1.0472; visualize minimum-action orbit | Blocker: no trusted billiard algorithm yet. See details below. |
| random-polytope-sys-distribution | Ideation (blocked) | How rare are counterexamples (sys > 1) among "natural" random polytope families? | ~1k samples, ≤16 facets, 4D. Compare families: convex hull of random points vs intersection of random halfplanes. Histogram of sys, split by family. Check if HKO is extremal or higher sys exist. Outcome determines targeted search vs random sampling. |
| lagrangian-product-polygons | Ideation (blocked) | What patterns emerge in systolic ratio for the (k, m, φ) family of Lagrangian polygon products? | k,m = polygon vertex counts, φ ∈ [0, 2π/m) rotation angle (WLOG by symmetry). Systematic + random sampling. Look for: global max, monotonic sequences, sys>1 fraction vs k, optimal φ(k,m). Exploratory — many independent analyses/plots. |
| lagrangian-product-random-polygons | Ideation (blocked) | What patterns emerge for Lagrangian products of random 2D polygons? | Random polygon families: convex hull of random points (various distributions), symmetry-constrained (central, rotational, mirror). Exploratory analysis with plots/tables/statistics. |
| fixed-facet-vertex-count | Ideation (blocked) | What can we say about sys distribution when fixing facet count or vertex count? | HK MSc thesis: simplices (5v/5f in 4D) have sys ≤ 3/4, unique max at orthonormal simplex. TODO: verify claim in HK thesis. Filter main random dataset by f-count/v-count, check distributions. |
| algorithm-performance-comparison | Ideation (blocked) | How do Billiard, HK2017, Tube compare in performance? What are the scaling laws? | Smaller instrumented dataset. Collect cputime, profiles, internal counters (tubes considered, permutations enumerated). Analyze cputime vs input params (facet count, etc). HK2017 is universal baseline. Identify hotspots. |
| algorithm-optimization-ablation | Ideation (blocked) | Which algorithmic components have what performance impact? Can we optimize without breaking correctness? | Keep trusted reference impl. Ablation study: toggle components, measure impact. Example: tube rotation upper bound — saves node visits but costs per-tube cpu. Cross-check ablation vs profiling. |
| 4d-polytope-visualization | Ideation | How to visualize 4D polytopes and Reeb dynamics in 3D/2D? | Pipeline: radial projection ∂K → S³ (v ↦ v/|v|, star-shaped w.r.t. 0), then stereographic S³ → R³, then 3D render. 2-faces → translucent curved surfaces, 1-faces → curved lines, 0-faces → points. Overlay: Reeb trajectories (arrows), tubes (translucent volumes), vector field. |
| dataset-dimension-reduction | Ideation (blocked) | Can we identify clusters/structures in the polytope dataset via dimension reduction? | 2D/3D scatter plots of numeric columns, filter by categoricals (family, facet count). PCA, UMAP for nonlinear. Regression models for mutual information between columns. |
| nn-regression-mutual-info | Ideation (blocked) | Can a NN find non-linear mutual information between polytope features and sys? | Extension of dimension reduction. NN as regression model to detect complex relationships that linear methods miss. |
| ml-capacity-prediction | Ideation (blocked) | Can ML learn a scalable (blackbox) capacity algorithm? How learnable is c_EHZ? | Explore dataset, architecture, training objective (noise, RL, subtasks like autoencoding for symplectomorphism invariance), input encoding (precomputed nonlinear features, redundant representations). Use capacity axioms (scaling, monotonicity, invariance, continuity) to relate rows / regularize. |
| sys-ratio-optimization | Ideation (blocked) | Can we optimize to find maximum systolic ratio? What do gradient flow lines look like? | Methods: rejection sampling, gradient descent (if subgradient computable in h-rep/v-rep), RL. Study sys-gradient flow: local/global optima, saddle points. Lie group Sp(4) ⋊ R⁴ acts with sys invariant → generators ⊥ sys-gradient. Quotient by Lie group: simpler flow? |
| benchmark-hk2017 | Executed | How does HK2017 runtime scale? Can we predict runtime from polytope parameters? | Naive enumeration only (GraphPruned disabled). Result: ~1µs/permutation, R²=0.9997. Budget: 8f→0.1s, 9f→1.3s, 10f→~10s. See FINDINGS.md in experiment module. |

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

**Outcomes:**
- ✓ Yes: reproduces correctly, looks right
- ✗ No: discrepancy → algorithm bug to investigate
- ? Maybe: looks good but need more validation angles

[proposed]

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

**Blockers:** Trusted capacity algorithm (Tube, HK2017, or Billiard)

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

**Blockers:** Billiard algorithm (works on Lagrangian products)

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

**Blockers:** Billiard algorithm

## fixed-facet-vertex-count

**Research question:** What can we say about sys distribution when we fix combinatorial complexity (facet count or vertex count)?

**Prior work (to verify):**
HK's MSc thesis reportedly shows that simplices in 4D (5 vertices ⟺ 5 facets) satisfy:
- sys ≤ 3/4
- Unique global maximum at the orthonormal simplex (up to symplectomorphisms — there are infinitely many maxima related by Sp(4) ⋉ R⁴, but they're all equivalent)

**Note on star-shapedness:** The "unit simplex" = conv{0, e₁, e₂, e₃, e₄} doesn't contain 0 in its interior, but capacity is still well-defined even for non-star-shaped polytopes. We ignore the extra translation needed.

**TODO:** Download HK's MSc thesis and verify:
- Did she prove sys ≤ 3/4 for simplices?
- Is the orthonormal simplex the unique maximum?
- Amend this research question based on what she actually proved

**Experiment:** Filter the main random polytope dataset by facet count or vertex count, examine the resulting sys distribution. Can we:
- Empirically confirm HK's result for simplices?
- Make analogous conjectures for other fixed counts (6-facet polytopes, 7-facet, ...)?

**Blockers:** Main dataset (depends on `random-polytope-sys-distribution`), HK thesis verification

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

**Blockers:** All three algorithms implemented and trusted

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

**Blockers:** Working algorithms, `algorithm-performance-comparison` to identify what's worth optimizing

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

**Blockers:** Main dataset populated (`random-polytope-sys-distribution`)

## nn-regression-mutual-info

**Research question:** Can a neural network find non-linear mutual information between polytope features and sys that linear methods miss?

**Motivation:** Extension of `dataset-dimension-reduction`. Linear regression and PCA only capture linear relationships. A neural network can learn arbitrary nonlinear functions.

**Approach:** Train NN as regression model: features → sys. If the NN achieves low loss, there's learnable structure. Analyze what the NN learned (feature importance, hidden representations).

**Relationship to other experiments:**
- Builds on `dataset-dimension-reduction`
- Simpler than `ml-capacity-prediction` (regression on extracted features vs learning capacity from raw polytope)

**Blockers:** Main dataset populated

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

**Blockers:** Large labeled dataset (capacity values from exact algorithms)

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

**Blockers:** Capacity algorithm (for evaluating sys), understanding of polytope space geometry

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
2. **GraphPruned not tested:** FFI only exposes Naive enumeration; GraphPruned is disabled due to known issues.
3. **FFI limit:** 10 facets maximum is enforced by the FFI.

**Files:**
- Experiment module: `packages/python_viterbo/src/viterbo/experiments/benchmark_hk2017/`
- Data: `packages/python_viterbo/data/benchmark-hk2017/`
- Detailed findings: `FINDINGS.md` in experiment module

**Future work:**
- Benchmark GraphPruned variant once FFI issues resolved
- Test larger facet counts by removing FFI limit
- Profile bottlenecks for optimization
