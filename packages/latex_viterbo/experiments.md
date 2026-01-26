# Experiments Tracking

Quick-scan table for all research questions and experiments. See `.claude/skills/experiment-workflow/` for the full workflow.

**Status values:** Ideation | Specified | In progress | Executed | Polished | Abandoned | Failed | Superseded

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
