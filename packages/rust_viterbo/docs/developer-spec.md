# Developer Specification for EHZ Capacity Algorithms

> **Audience:** Claude Code agents implementing the algorithms
> **Prerequisite:** Read thesis chapter ([algorithms.tex](../../latex_viterbo/chapters/algorithms.tex)) for mathematical background
> **Status:** This document consolidates all algorithm specifications. Implementation archived at tag `v0.1.0-archive`.

## Table of Contents

1. [Overview](#1-overview)
2. [Algorithm: Billiard (for Lagrangian Products)](#2-algorithm-billiard-for-lagrangian-products)
3. [Algorithm: Tube (for General Polytopes)](#3-algorithm-tube-for-general-polytopes)
4. [Algorithm: HK2019 QP (for General Polytopes)](#4-algorithm-hk2019-qp-for-general-polytopes)
5. [Geometric Foundations](#5-geometric-foundations)
6. [Test Fixtures (Ground Truth)](#6-test-fixtures-ground-truth)
7. [Implementation Lessons](#7-implementation-lessons)

---

## 1. Overview

### 1.1 Problem Statement

Given a convex polytope \(K \subset \mathbb{R}^4\) in H-representation:
```
K = \bigcap_i \{x \in \mathbb{R}^4 : \langle n_i, x \rangle \leq h_i\}
```
where \(n_i\) are unit outward normals and \(h_i > 0\) (ensuring \(0 \in \mathrm{int}(K)\)).

**Compute:** The Ekeland-Hofer-Zehnder capacity \(c_{\mathrm{EHZ}}(K)\) and a witness orbit achieving it.

### 1.2 Algorithm Applicability

| Algorithm | Domain | Complexity | Status (v0.1.0-archive) |
|-----------|--------|------------|-------------------------|
| Billiard | Lagrangian products \(K_1 \times K_2\) | \(O(n_1^3 \times n_2)\) | WORKS |
| Tube | General polytopes | \(O(F! \times \mathrm{poly}(F))\) | NoValidOrbits |
| HK2019 | General polytopes | \(O(F!)\) | INCOMPLETE |

### 1.3 Input Contract

```rust
struct PolytopeHRep {
    normals: Vec<[f64; 4]>,  // unit outward normals, ||n_i|| = 1
    heights: Vec<f64>,       // positive heights, h_i > 0
}
```

**Invariants:**
- `normals.len() == heights.len() >= 5` (minimum for bounded 4D polytope)
- All normals are unit vectors
- All heights are positive (implies \(0 \in \mathrm{int}(K)\))
- No NaN/Inf values

### 1.4 Output Contract

```rust
struct CapacityResult {
    capacity: f64,              // c_EHZ(K)
    witness: Option<WitnessOrbit>,
    diagnostics: Diagnostics,
}

struct WitnessOrbit {
    breakpoints: Vec<[f64; 4]>,  // Points on \partial K
    facet_sequence: Vec<usize>,  // Which facet each segment lies on
    segment_times: Vec<f64>,     // Time on each segment (sum = capacity)
}
```

---

## 2. Algorithm: Billiard (for Lagrangian Products)

> **Source:** Rudolf 2022, "The Minkowski Billiard Characterization of the EHZ Capacity"
> **Implementation status:** WORKS (tesseract=4.0, triangle=1.5)
> **Known bug:** Pentagon returns 2.127, expected 3.441

### 2.1 When to Use

Use for **Lagrangian products** \(K = K_1 \times K_2\) where:
- \(K_1 \subset \mathbb{R}^2_q\) (configuration space)
- \(K_2 \subset \mathbb{R}^2_p\) (momentum space)

**Detection:** All facet normals have form \((n_q, 0, 0, 0)\), \((0, n_q, 0, 0)\), \((0, 0, n_p, 0)\), or \((0, 0, 0, n_p)\).

### 2.2 Mathematical Basis

**Theorem (Rudolf 2022):** For \(K = K_1 \times K_2\):
```
c_{\mathrm{EHZ}}(K) = \min \text{T-length of } (K_1, K_2^\circ)\text{-Minkowski billiard trajectory}
```
where \(K_2^\circ\) is the polar body and T-length is measured with \(K_2\) as the unit ball.

**Theorem (Rudolf 2022, Theorem 4):** Optimal trajectory has at most 3 bounces for 2D polygons.

### 2.3 LP Formulation

For a 3-bounce trajectory on edges \((e_1, e_2, e_3)\) of \(K_1\):

**Variables:**
- \(t_1, t_2, t_3 \in [0,1]\): edge parameters (\(q_i = a_i + t_i(b_i - a_i)\))
- \(z_1, z_2, z_3\): epigraph variables

**Objective:** Minimize \(z_1 + z_2 + z_3\)

**Constraints:**
```
z_k \geq \langle d_k, v \rangle  for all vertices v of K_2^\circ
t_i \in [\text{MARGIN}, 1-\text{MARGIN}]  (avoid degeneracy)
```
where \(d_k = q_{k+1} - q_k\) is the direction vector.

**Constants (UNCITED engineering choices):**
- `EPS = 1e-10`: Numerical tolerance
- `MARGIN = 0.01`: Avoid edge endpoints
- `SEPARATION = 0.1`: Prevent coincident bounces on adjacent edges

### 2.4 Algorithm Steps

```
function billiard_capacity(K: PolytopeHRep) -> CapacityResult:
    // Step 1: Extract 2D factors
    (K1, K2) = extract_lagrangian_factors(K)
    if extraction fails:
        return Error("Not a Lagrangian product")

    // Step 2: Compute polar
    K2_polar = polar(K2)

    // Step 3: Enumerate all 2-bounce and 3-bounce trajectories
    best = +\infty

    // 2-bounce: all edge pairs
    for (i, j) in edge_pairs(K1):
        result = solve_2bounce_lp(K1, K2_polar, i, j)
        if result.t_length < best:
            best = result.t_length
            best_trajectory = result

    // 3-bounce: all edge triples
    for (i, j, k) in edge_triples(K1):
        result = solve_3bounce_lp(K1, K2_polar, i, j, k)
        if result.t_length < best:
            best = result.t_length
            best_trajectory = result

    // Step 4: Construct witness
    witness = construct_witness(best_trajectory, K1, K2)

    return CapacityResult {
        capacity: best,
        witness: witness,
    }
```

### 2.5 Data Structures

```rust
/// 2D convex polygon in H-rep form
struct Polygon2DSimple {
    vertices: Vec<[f64; 2]>,  // CCW order, computed from H-rep
    normals: Vec<[f64; 2]>,   // Outward edge normals (unit vectors)
    heights: Vec<f64>,        // Signed distances from origin (must be > 0)
}
// Invariant: Polygon = {x : \langle n_i, x \rangle \leq h_i for all i}

/// Lagrangian product decomposition
struct LagrangianFactors {
    k1: Polygon2DSimple,         // q-space polygon (K_1 \subset \mathbb{R}^2_q)
    k2: Polygon2DSimple,         // p-space polygon (K_2 \subset \mathbb{R}^2_p)
    q_facet_indices: Vec<usize>, // Maps K_1 facet i -> original 4D facet index
    p_facet_indices: Vec<usize>, // Maps K_2 facet i -> original 4D facet index
}

/// 2-bounce trajectory (most common minimum)
struct BilliardTrajectory {
    action: f64,                 // Total T-length = capacity
    q_points: [[f64; 2]; 2],     // Bounce points on \partial K_1
    q_facet_local: [usize; 2],   // Which K_1 facets hit
    p_vertex_local: [usize; 2],  // K_2 vertices supporting directions
    p_facet_local: [usize; 2],   // Which K_2 facets traversed
}

/// 3-bounce trajectory (when 2-bounce insufficient)
struct ThreeBounceTrajectory {
    action: f64,
    q_points: [[f64; 2]; 3],
    edge_params: [f64; 3],       // t \in [0,1] parameter on each edge
    q_facet_local: [usize; 3],
}

/// LP result for 3-bounce optimization
struct LPThreeBounceResult {
    t_length: f64,               // Objective value
    edge_params: [f64; 3],       // Optimal t_1, t_2, t_3
    edge_indices: [usize; 3],    // Which edges of K_1
}
```

### 2.6 Implementation Details

**Lagrangian Factor Extraction:**
1. Partition facet normals by which coordinates are nonzero
2. Classify as "q-space only" (coords 0-1) or "p-space only" (coords 2-3)
3. Sort both q and p facets by `atan2(normal.y, normal.x)` to recover CCW boundary order
4. Build 2D polygons and track original 4D facet indices for witness construction

**Polar Body Computation:**
For H-rep polygon \(\{x : \langle n_i, x \rangle \leq h_i\}\), polar has vertices at \(n_i/h_i\).

**Edge Index Convention (CRITICAL):**
- LP convention: Edge i goes from vertex[i] to vertex[(i+1) mod n]
- Polygon convention: Facet i has normal \(n_i\) and is the edge ending at vertex[i]
- Mapping: LP edge i corresponds to polygon facet (i+1) mod n

**LP Constraint Linearization:**
For 3-bounce constraint \(z_1 \geq \langle d_{12}, y \rangle\) with \(d_{12} = (a_2 - a_1) + t_2 \cdot e_2 - t_1 \cdot e_1\):
```
z_1 + coef_t1 * t_1 - coef_t2 * t_2 \geq const
where:
  const = \langle a_2 - a_1, y \rangle
  coef_t1 = \langle e_1, y \rangle
  coef_t2 = \langle e_2, y \rangle
```

**Separation Constraints (adjacent edges):**
For edges i, j where j = (i+1) mod n (sharing a vertex):
```
-(1-t_i) - t_j \geq SEPARATION - 1
```
This prevents bounces both approaching the shared vertex.

**Witness Construction (2-bounce):**
2 bounces in \(K_1\) create 4-segment orbit in \(\mathbb{R}^4\):
```
(q_a, p_0) -> (q_a, p_1) -> (q_b, p_1) -> (q_b, p_0) -> close
    on q_0       on p_1       on q_1       on p_0
```
where \(p_0, p_1\) are \(K_2\) vertices supporting directions \(\pm(q_b - q_a)\).

**Degeneracy Detection:**
- Interior bounce (\(t \in (\varepsilon, 1-\varepsilon)\)): require pairwise bounce distance > \(\varepsilon\)
- Boundary bounce (\(t \approx 0\) or 1): use 10x larger tolerance

### 2.8 Known Issues

1. **Pentagon bug:** Returns 2.127, expected 3.441 (HK-O 2024 Prop 1.4)
   - Root cause: Unknown, needs investigation
   - The HK-O counterexample is Pentagon x RotatedPentagon

2. **Witness segment_times:** Currently placeholder zeros
   - Capacity value is correct
   - Breakpoints and facet_sequence are correct
   - segment_times need derivation from Reeb flow equations (not implemented)
   - Previous formula attempt had 335% error on random polygons

3. **UNCITED formulas:**
   - Support function and polar duality (standard convex geometry, needs textbook cite)
   - LP epigraph formulation (Boyd & Vandenberghe, not cited)
   - MARGIN and SEPARATION values (ad-hoc engineering, no mathematical justification)

---

## 3. Algorithm: Tube (for General Polytopes)

> **Source:** Chaidez-Hutchings 2021, "Computing Reeb Dynamics on Polytopes"
> **Implementation status:** Returns NoValidOrbits on all tested polytopes
> **Thesis algorithm name:** Stoehler 2026

### 3.1 When to Use

Use for general convex polytopes, especially non-Lagrangian products.

**Requirement:** Polytope must have at least one non-Lagrangian 2-face (\(\omega(n_i, n_j) \neq 0\)).

### 3.2 Mathematical Basis

Search over **combinatorial classes** of closed Reeb orbits.

**Key insight:** A closed orbit on \(\partial K\) is determined by:
1. Facet sequence \((i_1, i_2, \ldots, i_k, i_1, i_2)\) -- which facets visited
2. Starting point on the first 2-face

**Branch-and-bound:** Build a tree of partial orbits ("tubes"), prune by:
- Emptiness: tube has no valid trajectories
- Rotation: accumulated rotation > 2 turns
- Action: minimum action in tube exceeds current best

### 3.3 Data Structures

```rust
/// Preprocessing cache for polytope 2-face data
struct PolytopeData {
    hrep: PolytopeHRep,           // Original polytope
    two_faces: Vec<TwoFaceData>,  // Non-Lagrangian 2-faces only
}

/// Per-2-face cached geometric data
struct TwoFaceData {
    i: usize,                    // First facet index (i < j by convention)
    j: usize,                    // Second facet index
    flow_direction: FlowDir,     // ItoJ or JtoI (sign of \omega(n_i, n_j))
    rotation: f64,               // \rho(F) \in (0, 0.5) turns
    polygon: Polygon2D,          // 2D vertices in trivialized coordinates
    centroid: [f64; 4],          // 4D centroid of face
    entry_normal: [f64; 4],      // Normal of entry facet
    vertices_4d: Vec<[f64; 4]>,  // Original 4D vertices
}

enum FlowDir { ItoJ, JtoI }  // Determined by sign(\omega(n_i, n_j))

/// Partial Reeb orbit with fixed combinatorial type
struct Tube {
    facet_sequence: Vec<usize>,  // [i_1, i_2, ..., i_k, i_{k+1}]

    // Geometry in 2D trivialized coordinates
    p_start: Polygon2D,          // Valid starting points
    p_end: Polygon2D,            // Valid ending points
    flow_map: AffineMap2D,       // Cumulative map: p_start -> p_end
    action_func: AffineFunc,     // Action as function of starting point

    rotation: f64,               // Total rotation (turns)
    action_lower_bound: f64,     // Cached min action over p_end
}

struct AffineMap2D {
    linear: [[f64; 2]; 2],  // 2x2 matrix A
    offset: [f64; 2],       // Translation b
    // Apply: x \mapsto Ax + b
}

struct AffineFunc {
    gradient: [f64; 2],  // Linear coefficients
    constant: f64,       // Constant term
    // Evaluate: f(x) = \langle gradient, x \rangle + constant
}

/// Algorithm configuration
struct TubeAlgorithmConfig {
    max_rotation: f64,          // Default: 2.0 (per CH2021 Prop 1.10)
    use_rotation_cutoffs: bool, // Default: true
    use_action_bounds: bool,    // Default: true
}
```

### 3.4 Algorithm Steps

```
function tube_capacity(K: PolytopeHRep) -> CapacityResult:
    // Step 1: Preprocess
    data = PolytopeData::new(K)  // Enumerates non-Lagrangian 2-faces

    if data.two_faces.is_empty():
        return Error("No non-Lagrangian 2-faces")

    // Step 2: Initialize search
    best_action = +\infty
    worklist = PriorityQueue()  // By action lower bound

    // Step 3: Create root tubes (one per 2-face)
    for face in data.two_faces:
        tube = create_root_tube(face)
        if tube.rotation <= 2 + \varepsilon:
            worklist.push(tube)

    // Step 4: Branch-and-bound
    while worklist not empty:
        tube = worklist.pop()

        // Pruning
        if action_lower_bound(tube) >= best_action:
            continue

        // Extend or close
        for ext in get_extensions(tube, data):
            if ext is Closure:
                (action, witness) = solve_closed_tube(ext)
                if action < best_action:
                    best_action = action
                    best_witness = witness
            else:  // Extension
                if ext.p_end not empty and ext.rotation <= 2 + \varepsilon:
                    worklist.push(ext)

    return CapacityResult { capacity: best_action, witness: best_witness }
```

### 3.5 Flow Map Formulas

For crossing from 2-face \(F_{ij}\) to \(F_{jk}\) along facet \(E_j\):

**Time to cross:**
```
t(p) = h_j \times (h_k - \langle n_k, p \rangle) / (2 \times \omega(n_j, n_k))
```
where p is the starting point in \(\mathbb{R}^4\).

**Flow map (in 2D trivialization):**
```
\phi: TF_{ij} \to TF_{jk}
```
The transition matrix \(\psi_F \in \mathrm{Sp}(2)\) encodes the symplectic structure.

**Rotation increment:**
```
\rho(F_{ij}) = (1/2\pi) \times \arccos(\tfrac{1}{2} \times \mathrm{tr}(\psi_{F_{ij}}))
```

### 3.6 Trivialization of 2-Faces

Each 2-face tangent space is 2D. Use quaternion structure for basis:

```
\tau_F(V) = (\langle V, J \cdot n_j \rangle, \langle V, K \cdot n_j \rangle)
```

where J, K are the quaternion matrices (see Section 5).

### 3.7 Closure Detection

A tube with sequence \([i_1, i_2, \ldots, i_m, i_1, i_2]\) is "closeable".

To find closed orbits:
1. Find fixed points of flow_map: solve \((A - I)x = -b\)
2. **Check if solution lies in p_start** (not p_end, which may be numerically degenerate)
3. Evaluate action = action_func(fixed_point)
4. Reconstruct 4D witness via barycentric interpolation

**Barycentric reconstruction:**
- Given 2D fixed point in trivialized coordinates
- Fan-triangulate the 2D polygon from vertex 0
- Find which triangle contains the point
- Compute barycentric weights \((w_0, w_1, w_2)\)
- Apply same weights to 4D vertices: \(p_{4d} = w_0 \cdot v_0 + w_1 \cdot v_1 + w_2 \cdot v_2\)

### 3.8 Implementation Details

**Preprocessing Pipeline:**
1. Validate polytope H-rep (tolerance 1e-6)
2. If any Lagrangian 2-faces exist, reject (algorithm incompatible)
3. If near-Lagrangian detected, perturb normals (seed=42, \(\varepsilon\)=1e-2)
4. For each facet pair (i,j) with \(\omega(n_i, n_j) \neq 0\):
   - Compute flow direction from sign of \(\omega\)
   - Compute rotation \(\rho(F)\) from transition matrix eigenvalues
   - Trivialize 2-face polygon to 2D
   - Cache 4D vertices for reconstruction

**Extension Algorithm:**
1. Compute flow map \(\phi\) from current 2-face to next
2. Apply \(\phi\) to p_end polygon
3. Intersect with new 2-face polygon
4. If empty, prune (no valid trajectories)
5. Compose: flow_map' = \(\phi \circ\) flow_map
6. Compose: action_func' = action_func + time_func
7. Accumulate: rotation' = rotation + \(\rho\)(new_face)

**Constants:**
| Tolerance | Value | Purpose |
|-----------|-------|---------|
| EPS_FEAS | 1e-10 | Vertex feasibility |
| EPS_DEDUP | 1e-8 | Vertex deduplication |
| EPS_LAGR | 1e-9 | Lagrangian detection |
| EPS_ROT | 0.01 | Rotation pruning margin |

### 3.9 Known Issues

1. **NoValidOrbits:** Returns this for ALL tested polytopes
   - Tesseract: Expected (has Lagrangian 2-faces, algorithm rejects or perturbs)
   - Random non-Lagrangian: Rotation accumulates to ~1.25, 1.50 (not reaching closure)
   - 24-cell: Rotations 0.5-0.7 per face, doesn't close

2. **Possible causes:**
   - Rotation formula may have sign/convention error
   - Closure condition may be too strict
   - Test polytopes may not have short periodic orbits of required type
   - CH2021 uses specially constructed polytopes; generic ones may not work

3. **UNCITED formulas:**
   - Orthonormal basis approach for inverse trivialization
   - Time formula t(p) needs CH2021 section 2.2 velocity formula citation
   - Flow map linearity decomposition

---

## 4. Algorithm: HK2019 QP (for General Polytopes)

> **Source:** Haim-Kislev 2017, "On the Symplectic Size of Convex Polytopes"
> **Implementation status:** INCOMPLETE (only checks vertices+edges, misses higher-dim faces)
> **Tests pass by luck:** Optima for tesseract happen to be at vertices

### 4.1 When to Use

Works for ANY convex polytope, but \(O(F!)\) complexity limits to ~10 facets.

### 4.2 Mathematical Basis

**Theorem (HK2017 Theorem 1):** For K with F facets:
```
c_{\mathrm{EHZ}}(K) = \frac{1}{2} \times [\max_{\sigma,\beta} Q(\sigma,\beta)]^{-1}
```

where the Q-function is:
```
Q(\sigma,\beta) = \sum_{j<i} \beta_{\sigma(i)} \times \beta_{\sigma(j)} \times \omega(n_{\sigma(i)}, n_{\sigma(j)})
```

**Constraints:**
- \(\sigma \in S_F\) (permutation of facets)
- \(\beta \geq 0\) (non-negative weights)
- \(\sum_i \beta_i \times h_i = 1\) (height normalization)
- \(\sum_i \beta_i \times n_i = 0\) (closure: 4 equations)

### 4.3 QP Formulation

**This is NON-CONVEX optimization:**
- Q is indefinite quadratic (neither convex nor concave)
- Optimum can be at vertices, edges, 2-faces, or higher-dimensional faces of feasible region

**Two equivalent formulations:**

1. **Maximize indefinite Q over polytope** (our implementation attempt)
2. **QCQP:** Minimize \((\sum \beta_i h_i)^2\) subject to Q=1 (quadratic equality constraint)

Both are NP-hard in general.

### 4.4 Algorithm Steps (INCOMPLETE)

```
function hk2019_capacity(K: PolytopeHRep) -> CapacityResult:
    best_q = 0

    // Enumerate permutations (F! of them)
    for \sigma in permutations(0..F):
        q_max = solve_qp_for_permutation(K, \sigma)
        if q_max > best_q:
            best_q = q_max
            best_\sigma = \sigma

    return CapacityResult {
        capacity: 0.5 / best_q,
        ...
    }
```

**CRITICAL BUG in `solve_qp_for_permutation`:**
- Only checks vertices (0D) and edges (1D) of feasible polytope
- For 3D+ feasible regions, optimum may be on 2D or higher faces
- Would need global QCQP solver (SCIP, Gurobi, etc.)

### 4.5 Implementation Details

**Constraint Matrix Setup:**
- \(5 \times n\) matrix A (5 constraints, n facets)
- Row 0: height values \(h_i\)
- Rows 1-4: four components of normal vectors \(n_i\)
- Right-hand side: b = [1, 0, 0, 0, 0]

**Vertex Enumeration (Phase 1):**
1. Enumerate subsets S with \(|S| \leq \min(n, 5)\)
2. Extract reduced system \(A_S\) by selecting columns for S
3. Solve \(A_S \times \beta_S = b\) via SVD
4. Check feasibility: \(\|A_S \times \beta_S - b\| < 10^{-8}\) and \(\beta_i \geq -10^{-10}\)
5. Evaluate Q at each vertex

**Edge Interior Search (Phase 2):**
1. For each vertex pair \((v_1, v_2)\), parameterize \(\beta(t) = (1-t)v_1 + tv_2\)
2. Restrict Q to edge: \(Q(t) = at^2 + bt + c\)
3. Compute coefficients from three points (t=0, 0.5, 1)
4. Find critical point \(t^* = -b/(2a)\)
5. If parabola opens downward (\(a < -10^{-12}\)) and \(t^* \in (0,1)\), evaluate \(Q(t^*)\)

**Constants:**
| Constant | Value | Purpose |
|----------|-------|---------|
| MAX_FACETS | 10 | Refuse >10 facets |
| DEFAULT_TIMEOUT | 60s | Prevent runaway |
| Residual tol | 1e-8 | Vertex feasibility |
| \(\beta\) tolerance | -1e-10 | Allow small negative |

### 4.6 Why Tests Pass

For the tesseract, the optimal Q = 0.125 happens to occur at a vertex:
- \(\beta = (0.25, 0.25, 0.25, 0.25, 0, 0, 0, 0)\) for appropriate permutation
- This is a degenerate case; general polytopes may have interior optima

### 4.6 To Fix

1. Implement proper QCQP solver in `optim` crate
2. Or use external solver (SCIP, Gurobi, BARON)
3. Or reformulate as mixed-integer program

---

## 5. Geometric Foundations

### 5.1 Coordinate Convention

Standard symplectic \(\mathbb{R}^4\) with coordinates \((q_1, q_2, p_1, p_2)\):
- \(q = (q_1, q_2)\): configuration space
- \(p = (p_1, p_2)\): momentum space

### 5.2 Almost Complex Structure J

```
J: \mathbb{R}^4 \to \mathbb{R}^4
J(q_1, q_2, p_1, p_2) = (-p_1, -p_2, q_1, q_2)
```

Matrix form:
```
J = [ 0   0  -1   0 ]
    [ 0   0   0  -1 ]
    [ 1   0   0   0 ]
    [ 0   1   0   0 ]
```

Properties: \(J^2 = -I\), \(J^T = -J\)

### 5.3 Symplectic Form

```
\omega(x, y) = \langle Jx, y \rangle = q_1 p_1' + q_2 p_2' - p_1 q_1' - p_2 q_2'
```

Properties:
- Antisymmetric: \(\omega(x,y) = -\omega(y,x)\)
- Non-degenerate: \(\omega(x,y)=0 \;\forall y \Rightarrow x=0\)

**Standard basis:**
```
\omega(e_1, e_3) = 1   (q_1, p_1 canonical pair)
\omega(e_2, e_4) = 1   (q_2, p_2 canonical pair)
\omega(e_1, e_2) = 0   (Lagrangian)
\omega(e_3, e_4) = 0   (Lagrangian)
```

### 5.4 Quaternion Structure

For 2-face trivialization, use quaternion matrices:

```
I = identity

J = [ 0   0  -1   0 ]    (same as complex structure)
    [ 0   0   0  -1 ]
    [ 1   0   0   0 ]
    [ 0   1   0   0 ]

K = [ 0  -1   0   0 ]
    [ 1   0   0   0 ]
    [ 0   0   0   1 ]
    [ 0   0  -1   0 ]
```

Relations: \(I^2 = J^2 = K^2 = IJK = -I\)

### 5.5 Trivialization \(\tau_n\)

Maps 4D vectors to 2D coordinates via projection onto 2-face plane:

```
\tau_n(V) = (\langle V, J \cdot n \rangle, \langle V, K \cdot n \rangle)
```

**Key property:** Preserves symplectic form: \(\omega(V_1, V_2) = \omega_0(\tau_n(V_1), \tau_n(V_2))\)

**Transition matrix:** For 2-face F with entry normal \(n_1\) and exit normal \(n_2\):
```
\psi_F = \tau_{n_2} \circ (\tau_{n_1})^{-1}
```

Properties:
- \(\psi_F \in \mathrm{Sp}(2)\) (symplectic)
- For non-Lagrangian F: \(\psi_F\) is positive elliptic (\(|\mathrm{tr}| < 2\))

### 5.6 Lagrangian Detection

A 2-face \(F_{ij} = E_i \cap E_j\) is **Lagrangian** iff:
```
\omega(n_i, n_j) = 0
```

**Perturbation:** If \(|\omega(n_i, n_j)| < \varepsilon_{\mathrm{lagr}}\), perturb normals:
- Seeded RNG for reproducibility
- Add random \(\delta\) scaled by \(\varepsilon\) to each normal
- Re-normalize to unit length

### 5.7 Rotation Number

For non-Lagrangian 2-face F, the transition matrix \(\psi_F \in \mathrm{Sp}(2)\).

```
\rho(F) = \frac{1}{2\pi} \times \arccos(\tfrac{1}{2} \times \mathrm{tr}(\psi_F))
```

**Sp(2) classification:**
- \(|\mathrm{tr}| > 2\): Hyperbolic
- \(|\mathrm{tr}| = 2\): Parabolic (shear)
- \(|\mathrm{tr}| < 2\): Elliptic (rotation)

For non-Lagrangian faces: \(\rho(F) \in (0, 0.5)\) (positive elliptic).

---

## 6. Test Fixtures (Ground Truth)

### 6.1 Literature Values

| Polytope | \(c_{\mathrm{EHZ}}\) | Source | Billiard | HK2019 | Tube |
|----------|-------|--------|----------|--------|------|
| Tesseract \([-1,1]^4\) | 4.0 | HK2019 Ex 4.6 | 4.0 | 4.0 | NoValidOrbits |
| Rectangle 2x1 product | 1.0 | Scaling axiom | 1.0 | 1.0 | NoValidOrbits |
| Triangle x Triangle | 1.5 | Computational | 1.5 | 1.5 | NoValidOrbits |
| Pentagon x Rotated | 3.441 | HK-O 2024 | 2.127 (BUG) | timeout | NoValidOrbits |
| 4-Simplex | 0.25 | Y. Nir 2013 | N/A | OK | ? |

### 6.2 Tesseract Definition

```rust
fn tesseract() -> PolytopeHRep {
    // [-1,1]^4 = [-1,1]^2 \times [-1,1]^2
    normals: [
        [1, 0, 0, 0], [-1, 0, 0, 0],  // \pm q_1
        [0, 1, 0, 0], [0, -1, 0, 0],  // \pm q_2
        [0, 0, 1, 0], [0, 0, -1, 0],  // \pm p_1
        [0, 0, 0, 1], [0, 0, 0, -1],  // \pm p_2
    ],
    heights: [1, 1, 1, 1, 1, 1, 1, 1],
}
```

### 6.3 Triangle x Triangle Definition

Equilateral triangle with circumradius 1:
```rust
fn triangle_product() -> PolytopeHRep {
    let r = 1.0;  // circumradius
    // Vertices at angles 0 deg, 120 deg, 240 deg
    // Facet normals point outward from edges
    // K_1 and K_2 are the same triangle
    ...
}
```

Expected capacity: \(c = 1.5 \times r^2 = 1.5\)

### 6.4 Pentagon x Rotated Pentagon (HK-O Counterexample)

Regular pentagon K with circumradius 1, T = K rotated by 90 deg.

```
c_{\mathrm{EHZ}}(K \times T) = 2 \times \cos(\pi/10) \times (1 + \cos(\pi/5)) \approx 3.4409548...
```

**Significance:** Systolic ratio \(\rho = 1.047 > 1\), contradicting Viterbo's conjecture.

---

## 7. Implementation Lessons

### 7.1 What Worked

1. **Billiard LP:** Clean mathematical formulation, LP solvers reliable
2. **Proptest:** Random testing caught edge cases
3. **Modular design:** Separate geom/algorithm/ffi crates

### 7.2 What Didn't Work

1. **HK2019 QP:** Non-convex optimization is hard; vertex enumeration insufficient
2. **Tube NoValidOrbits:** Either rotation formula wrong or test polytopes unsuitable
3. **Witness times:** Converting billiard to Reeb orbit requires more work

### 7.3 Recommendations for Re-implementation

1. **Start with Billiard:** Most reliable, clearest math
2. **Use established QP solvers:** Don't write your own for HK2019
3. **Test on CH2021 polytopes:** Their paper has specific examples with known orbits
4. **Add rotation formula tests:** Verify against analytical examples

---

## References

- **CH2021:** Chaidez-Hutchings, "Computing Reeb Dynamics on Four-Dimensional Convex Polytopes"
- **HK2017:** Haim-Kislev, "On the Symplectic Size of Convex Polytopes"
- **HK-O 2024:** Haim-Kislev & Ostrover, "A Counterexample to Viterbo's Conjecture"
- **Rudolf 2022:** "The Minkowski Billiard Characterization of the EHZ-Capacity"
- **Y. Nir 2013:** "On Closed Characteristics and Billiards in Convex Bodies" (thesis)
