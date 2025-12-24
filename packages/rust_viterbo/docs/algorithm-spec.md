# Capacity Algorithm Spec (tube algorithm, working contract)

This file is an **implementer-facing contract** for the Rust capacity algorithm.

- Scope: computation in \(\mathbb{R}^4\) only (toy tests in lower dimensions are fine).
- Non-goals: Lean formalization; requiring callers to provide multiple polytope representations.

Status: this is a **living** contract. It captures decisions that are stable enough to delegate
implementation against, but the algorithm and its numerical details will evolve as we learn.

Locked constraints were confirmed on **2025-12-22**; the **main input contract** was updated on
**2025-12-24**.

## 1) Goal

Implement a routine that computes (numerically) a value for
\[
  c_{\mathrm{EHZ}}(K)
\]
for a convex polytope \(K \subset \mathbb{R}^4\), and returns a **witness orbit** sufficient for
validation/debugging/visualization.

The intended replication target is the HK\&O counterexample via **our tube-based algorithm**.

## 2) Conventions (must match the thesis)

- Coordinates: \((q_1,q_2,p_1,p_2)\).
- Almost complex structure: \(J(q,p)=(-p,q)\).
- Standard symplectic form: \(\omega(x,y)=\langle Jx, y\rangle\).
- Polytope H-representation (irredundant):
  \[
    K = \bigcap_i \{x : \langle n_i, x\rangle \le h_i\}
  \]
  with outward **unit** normals \(n_i \in \mathbb{R}^4\), heights \(h_i>0\).

## 3) Input contract

### 3.1 Required polytope representations

Owner decision (2025-12-24):

- The main capacity routine (and its Python FFI entrypoint) accepts **only** an irredundant H-rep:
  `(normals, heights)`.
- No optional V-rep input.
- If subroutines need V-rep (e.g. for volume/systolic ratio computations), Rust may compute it
  internally (and should report relevant costs/metadata in diagnostics).

### 3.2 Geometry invariants

The algorithm assumes:

- \(K\) is convex, bounded, and full-dimensional in \(\mathbb{R}^4\).
- \(0 \in \mathrm{int}(K)\).
- H-rep is irredundant; normals are outward and unit; heights are positive.

Contract enforcement:

- Rust-internal entrypoints may assume invariants (with `debug_assert!`).
- FFI entrypoints must validate and return structured errors even in release builds.

## 4) Output contract

Return:

1) **Capacity estimate**: a `f64` value for \(c_{\mathrm{EHZ}}(K)\).

2) **Witness orbit**:
   - Minimal acceptable payload: `breakpoints` (cyclic list of points in \(\mathbb{R}^4\)).
   - Preferred (redundant) payload for datasets/debugging:
     - `breakpoints`
     - `segment_times`
     - `segment_facets` (facet indices)

3) **Diagnostics** (minimum useful set):
   - explored node count, pruned-by-reason counts (emptiness/action/rotation),
   - best lower/upper bounds seen (if applicable),
   - perturbation metadata when used (seed, epsilon, eps_lagr, etc.).

## 5) Algorithm: tube-based branch-and-bound (high-level)

We search over **combinatorial classes** (“tubes”) of polygonal Reeb trajectories on \(\partial K\).

Each search node represents a partial facet sequence (and corresponding 2-face transitions) and stores
enough data to:

- decide whether the tube is empty,
- compute a **lower bound** on the action of any closed orbit in its subtree,
- extend the tube by one transition.

The concrete tube data structures and update formulas live in the thesis write-up; this document only
states the PM/implementation contract.

Pruning must include:

- **emptiness pruning**: tube becomes empty \(\Rightarrow\) prune subtree,
- **action pruning**: if a tube’s lower bound is \(\ge\) current best upper bound, prune subtree,
- **rotation pruning** (see §6): discard only if rotation \(> 2 + \varepsilon_{\mathrm{rot}}\).

## 6) Rotation pruning (MVP, owner-locked)

We use Chaidez–Hutchings (2021) combinatorial rotation number:

- Units: **turns** (1 turn = \(2\pi\)).
- Threshold: keep \(\rho_{\mathrm{comb}} \le 2\).
- Numeric robustness: discard only if \(\rho_{\mathrm{comb}} > 2 + \varepsilon_{\mathrm{rot}}\).

Edge case:

- Orbits flowing along 1-faces/edges are treated as having rotation \(+\infty\) (per CH2021) and are
  not candidates for minimizers under this pruning regime.

## 7) Lagrangian 2-faces and perturbation (MVP, owner-locked)

Definitions:

- A 2-face \(F_i \cap F_j\) is Lagrangian iff \(\omega(n_i,n_j)=0\).
- A polytope is treated as “Lagrangian” if it has **any** Lagrangian 2-faces (numerically, within a tolerance).

Operational policy (owner-locked):

- Public/FFI entrypoints should detect whether \(K\) has (numerically) Lagrangian 2-faces and, if yes,
  apply a seeded perturbation to facet normals (heights fixed) before running the tube algorithm.
- The tube algorithm implementation itself keeps the same signature
  (`H-rep -> capacity + witness + diagnostics`) regardless of whether perturbation was used.

Deferred details (must be implemented, but not yet locked):

- concrete perturbation scheme and epsilon schedule,
- concrete tolerance values: `eps_lagr`, `eps_rot`, geometry epsilons.

## 8) Immediate implementation milestones (delegable)

1) Polytope types + validation (H/V rep, invariants, conventions).
2) 2-face extraction + polygon representation (and adjacency/transition data).
3) Tube state + extension + closure detection; action lower bound computation.
4) Branch-and-bound traversal + diagnostics.
5) Rotation pruning integration (CH2021 units, threshold, robust discard rule).
6) Regression targets (HK\&O product, cube, simplex, a non-Lagrangian example) with tolerances to be calibrated.

## 9) Testing & validation (required for “we trust the implementation”)

The goal of the test suite is not “coverage”; it is to prevent us from shipping a numerically plausible
but mathematically wrong implementation.

Tests should exist at three levels:

### 9.1 Rust unit tests (fast, deterministic)

Focus: primitives where mistakes are easy and catastrophic.

- **Linear algebra conventions**:
  - `J` convention (signs/order of \((q,p)\)).
  - \(\omega(x,y)=\langle Jx, y\rangle\) identity tests.
- **Lagrangian detection**:
  - if \(|\omega(n_i,n_j)| \le \mathrm{eps\_lagr}\) then the 2-face is treated as Lagrangian.
- **Rotation bookkeeping**:
  - confirm units are **turns** throughout (no \(2\pi\) mixing),
  - confirm pruning rule is “discard only if \(\rho_{\mathrm{comb}} > 2 + \varepsilon_{\mathrm{rot}}\)”.

### 9.2 Rust integration tests (tube algorithm correctness scaffolding)

These tests are allowed to be “math-light”: they validate internal consistency and invariants.

- **Witness verification** (for any returned orbit):
  - breakpoints are cyclic and lie on \(\partial K\) (within tolerance),
  - each segment lies in a single facet (the facet index is consistent with active constraints),
  - segment direction matches the Reeb direction for that facet (within tolerance),
  - `action == sum(segment_times)` (within tolerance).
- **Reordering invariance**:
  - permuting facet order and vertex order in the input must not change the output value (beyond tolerance).
- **Determinism**:
  - for non-Lagrangian inputs (no perturbation), results are deterministic.

### 9.3 Python smoke/regression tests (FFI end-to-end, catch integration drift)

These are the most valuable “did we break the pipeline?” tests.

- **HK\&O replication regression**:
  - run the capacity routine via FFI on the HK\&O polytope produced by
    `packages/python_viterbo/src/viterbo/experiments/counterexample_hko/stage_build.py`,
  - compare to the known closed-form value (tolerance to be calibrated after first implementation),
  - record perturbation metadata (seed/epsilon/eps_lagr) in test output.
- **FFI input validation tests** (negative tests):
  - mismatch lengths (normals vs heights vs vertices),
  - non-unit normals, negative heights, NaNs/infs,
  - inconsistent H-rep vs V-rep should be rejected (or at least loudly warned, depending on chosen validation strictness).

### 9.4 Property tests (recommended, once the first implementation runs)

Use `proptest`/randomized tests where the expected behavior is mathematically constrained.

Suggested properties:

- **Scaling (2-homogeneity)**:
  - scale \(K\) by \(\lambda\) (heights and vertices scale by \(\lambda\)),
  - check \(c_{\mathrm{EHZ}}(\lambda K) \approx \lambda^2 c_{\mathrm{EHZ}}(K)\).
- **Symplectic invariance (restricted family)**:
  - apply simple linear symplectic transforms we can generate and apply robustly
    (e.g. block rotations in each \((q_i,p_i)\) plane),
  - check capacity is unchanged (within tolerance).
- **Monotonicity sanity check**:
  - if we form a strict superset polytope by increasing all heights by a factor \(>1\),
  - check capacity does not decrease (within tolerance).

Note: perturbation-policy tests (Lagrangian case) are intentionally deferred until we lock a concrete
epsilon schedule and tolerance calibration.

## 10) Benchmarking & profiling (required to avoid “slow but correct” surprises)

Benchmarks must measure:

- runtime (wall time and allocations),
- algorithmic behavior (search explosion / pruning efficiency),
- **scaling laws**: which polytope features make instances expensive,
- **hotspots**: where time is spent (so we optimize the right thing).

### 10.1 What to benchmark

Minimum benchmark set (representative, not exhaustive):

- a small non-Lagrangian polytope (few facets) to measure overhead,
- HK\&O (Lagrangian → perturb → tube algorithm) as the primary “real” case,
- a medium random-ish non-Lagrangian polytope (to measure scaling behavior).

To understand scaling and “hard instances”, include small sweeps over families:

- same polytope family with increasing size (e.g. facet count) to estimate scaling trends,
- at least one near-degenerate family (nearly Lagrangian 2-faces, very small facets, very shallow angles),
- (optional) compare centrally symmetric vs generic instances if we expect pruning/search behavior to differ.

### 10.2 What to record (per run)

Bench harness should record:

- wall time,
- allocation metrics (at least total allocations/bytes, if feasible),
- nodes explored,
- pruned-by-reason counts (emptiness/action/rotation),
- best upper bound evolution (optional, but useful),
- perturbation metadata when used (seed/epsilon/eps_lagr).

To enable scaling-law analysis, also record **instance descriptors** (input complexity):

- `num_facets`, `num_vertices`,
- `num_2faces` and basic 2-face graph stats (degree distribution, strongly connected components, etc.),
- count of (numerically) Lagrangian / near-Lagrangian 2-faces (and summary stats of \(|\omega(n_i,n_j)|\)),
- basic degeneracy indicators (e.g. min/max facet area proxies, min dihedral-angle proxy if available).

And record **algorithm descriptors** (behavior/structure):

- attempted tube extensions,
- closeable tubes encountered,
- per-depth node counts (how fast the tree explodes),
- (if cheap) summary of tube polygon complexity (e.g. average vertex count of `P_end`).

### 10.3 Tooling suggestions (implementation detail)

- Rust: `criterion` benches are a good default (`cargo bench`).
- Keep benchmarks deterministic (fixed inputs; fixed RNG seeds).
- Profile only after correctness tests pass; optimize only after profiling.

For profiling/hotspots:

- CPU hotspots: `cargo flamegraph` / `perf` on `--release` builds.
- Allocations: consider `dhat`/heap profiling (only after correctness is stable).
- Prefer adding lightweight timing spans (e.g. via `tracing`) around major phases:
  - polytope validation / parsing,
  - face extraction,
  - tube extension + polygon intersection,
  - rotation updates,
  - closure solve + witness extraction.

For scaling-law plots:

- export benchmark results to a stable machine-readable format (JSON/CSV),
- plot runtime and search stats as a function of `num_facets`, `num_2faces`, graph stats, and degeneracy indicators.
