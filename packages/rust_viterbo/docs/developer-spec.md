# Developer Specification for EHZ Capacity Algorithms

> **⚠️ DEPRECATED** — This is the v1 spec. See **[developer-spec-v2.md](developer-spec-v2.md)** for the current specification.
>
> This document is retained for historical reference. The v2 spec focuses on the Tube algorithm with improved mathematical rigor and resolved ambiguities.

---

> **Audience:** Claude Code agents implementing the algorithms
> **Prerequisite:** Read thesis chapter ([algorithms.tex](../../latex_viterbo/chapters/algorithms.tex)) for mathematical background
> **Status:** DEPRECATED. Implementation archived at tag `v0.1.0-archive`.

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

**Input:** A polytope \(K \subset \mathbb{R}^4\) with \(0 \in \mathrm{int}(K)\).

**Equivalent definitions of "polytope":**
- Convex hull of finitely many vertices, with nonempty interior
- Intersection of finitely many half-spaces, bounded, with nonempty interior

**Representations:**
- **H-representation (half-space):** \(K = \bigcap_i \{x \in \mathbb{R}^4 : \langle n_i, x \rangle \leq h_i\}\)
- **V-representation (vertex):** \(K = \mathrm{conv}(\{v_1, \ldots, v_m\})\)

Either representation can be used as input. This spec focuses on H-rep because the algorithms work directly with facet normals, but V-rep is equally valid (convert via vertex enumeration or facet enumeration).

**Conventions for H-rep:**
- **Non-redundant:** Every half-space defines a facet (no inequality is implied by others)
- **Normalized:** Normals are outwards pointing unit vectors (\(\|n_i\| = 1\)) and heights are positive (\(h_i > 0\), which follows from \(0 \in \mathrm{int}(K)\))

**Conventions for V-rep:**
- **Non-redundant:** Every vertex is an extreme point (not a convex combination of others)

**Representing a Polytope:**
```rust
struct PolytopeRepEnriched {
    num_facets: usize,
    normals: Vec<[f64; 4]>,
    heights: Vec<f64>,
    num_vertices: usize,
    vertices: Vec<[f64; 4]>,
}

impl PolytopeRepEnriched {
    fn is_valid(&self) -> bool {
        // H-rep validity:
        //   normals.len() == heights.len() == num_facets
        //   ||normals[i]|| == 1.0 for all i
        //   heights[i] > 0.0 for all i
        //   the intersection of half-spaces is bounded
        //   the half-spaces are non-redundant (none can be removed without changing K)
        //
        // V-rep validity:
        //   vertices.len() == num_vertices
        //   the convex hull contains 0 in its interior
        //
        // Cross-validation:
        //   conv(vertices) == intersection of half-spaces
        todo!()
    }
}
```

**Compute:** The Ekeland-Hofer-Zehnder capacity \(c_{\mathrm{EHZ}}(K)\) and a minimum action closed Reeb orbit on \(\partial K\) achieving it.

**Definitions / Representations of Reeb orbit:**
- fully general: \( \gamma \in W^{1,2}([0,T], \partial K) \) with \( \int_0^T \dot\gamma(t) dt = 0 \) (closed) and \( \dot\gamma(t) \in \mathrm{conv}\{ 2/h_i J n_i : \gamma(t) \in F_i \} \) (Reeb flow differential inclusion) where \(F_i\) are the facets of \(K\) and \(R_i = 2/h_i J n_i\) are the Reeb vectors on each facet.
- Reeb orbits can be piecewise linear, which can be represented by a cyclic sequence of breakpoints and break times \(\{(p_k, t_k)\}_{k=1}^N \subset \mathbb{R}^4 \times [0,T]\) with \(0 = t_1 < t_2 < \ldots < t_{N+1} = T\) and period \(T>0\). The segments lie on the polytope boundary, the breakpoints in particular have to lie on facet boundaries i.e. in the interior of a 0,1,2-face.
- There always is a minimum action Reeb orbit that is piecewise linear, and takes every velocity \((p_{k+1} - p_k)/ (t_{k+1} - t_k)\) equal to some facet Reeb vector \(R_{i_k}\) (theorem in thesis) and even takes every Reeb vector at most once.
- If the polytope has no lagrangian 2-faces, then all segments lie on the interior of 3-facets, i.e. no facet flows along a 0,1,2-face.
- Some polytopes with lagrangian 2-faces have only minimum action orbits such that the orbit flows along a lagrangian 2-face with a breakpoint in the interior of the lagrangian 2-face.

**Representation of Reeb orbits in output:**
```rust
struct SimpleReebOrbitEnriched {
    period: f64,                // also equals the action
    num_segments: usize,
    breakpoints: Vec<[f64; 4]>, // points on the boundary
    breaktimes: Vec<f64>,       // cumulative times at each breakpoint
    segment_facets: Vec<usize>, // which facet each segment lies on
}

impl SimpleReebOrbitEnriched {
    fn is_valid(&self, K: &PolytopeHRep) -> bool {
        // Array lengths:
        //   breakpoints.len() == num_segments + 1
        //   breakpoints[num_segments] == breakpoints[0]  (closed)
        //   breaktimes.len() == num_segments + 1
        //   breaktimes[0] == 0.0, breaktimes[num_segments] == period
        //   segment_facets.len() == num_segments
        //
        // Timing:
        //   breaktimes strictly increasing
        //
        // Geometry (for each segment k):
        //   breakpoints[k] and breakpoints[k+1] lie on facet segment_facets[k]
        //   velocity (breakpoints[k+1] - breakpoints[k]) / (breaktimes[k+1] - breaktimes[k])
        //     equals Reeb vector R_i = (2/h_i) * J * n_i on that facet
        //
        // Simplicity:
        //   no facet appears twice in segment_facets
        todo!()
    }
}
```

### 1.2 Algorithm Applicability

| Algorithm | Domain | Complexity | Status (v0.1.0-archive) |
|-----------|--------|------------|-------------------------|
| Billiard | Lagrangian products \(K_1 \times K_2\) | \(O(n_1^3 \times n_2)\) | WORKS |
| Tube | General polytopes | \(O(F! \times \mathrm{poly}(F))\) | NoValidOrbits |
| HK2019 | General polytopes | \(O(F!)\) | INCOMPLETE |

### 1.3 Input Contract

We minimize the amount of data to pass into the function, it can enrich on the fly as needed:
```rust
struct PolytopeHRep {
    normals: Vec<[f64; 4]>,  // unit outward normals, ||n_i|| = 1
    heights: Vec<f64>,       // positive heights, h_i > 0
}
```
The invariants are as one can deduce from the previous "enriched" struct.
And from common sense, e.g. no NaNs ever.

### 1.4 Output Contract

```rust
struct CapacityResult {
    capacity: f64,              // c_EHZ(K)
    orbit: Option<ReebOrbit>,   // Minimum action closed Reeb orbit
    diagnostics: Diagnostics,
}

struct ReebOrbit {
    breakpoints: Vec<[f64; 4]>,  // Points on \partial K where the velocity changes, breakpoints[0] == breakpoints[breakpoints.len()-1]
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

**Detection:** All facet normals have form \((n_q, 0), (0, n_p)\) where \(n_q, n_p \in \mathbb{R}^2\).

**Representation**:

```rust
struct LagrangianProductPolytope {
    K1: PolygonFactor,  // 2D polygon K_1 in H-rep
    K2: PolygonFactor,  // 2D polygon K_2 in H-rep
}
struct PolygonFactor {
    num_facets: usize,
    normals: Vec<[f64; 2]>,  // unit outward normals in R^2
    heights: Vec<f64>,       // positive heights
    num_vertices: usize,
    vertices: Vec<[f64; 2]>, // computed from H-rep
}

impl PolygonFactor {
    fn is_valid(&self) -> bool {
        // H-rep validity (same as 4D case):
        //   normals.len() == heights.len() == num_facets
        //   ||normals[i]|| == 1.0
        //   heights[i] > 0.0
        //   intersection is bounded
        //
        // V-rep validity:
        //   vertices.len() == num_vertices
        //   0 in interior of conv(vertices)
        //
        // Cross-validation:
        //   conv(vertices) == intersection of half-spaces
        //
        // 2D-specific ordering:
        //   num_vertices == num_facets (polygon property)
        //   facets and vertices in CCW order
        //   edge from vertices[k] to vertices[(k+1) % n] lies on facet k
        todo!()
    }
}
```

### 2.2 Mathematical Basis

**Theorem (Rudolf 2022):** For \(K = K_1 \times K_2\):
```
c_{\mathrm{EHZ}}(K) = \min \text{T-length of } (K_1, K_2^\circ)\text{-Minkowski billiard trajectory}
```
where \(K_2^\circ\) is the polar body and T-length is measured with \(K_2\) as the unit ball.

**Theorem (Rudolf 2022, Theorem 4):** Optimal trajectory has at most 3 bounces for 2D polygons as factors.

### 2.3 Algorithm Overview

We search for minimum-action Reeb orbits that are **k-bounce billiard trajectories**:
- A piecewise linear closed curve on \(\partial(K_1 \times K_2)\)
- Segments alternate between \((\partial K_1) \times K_2\) and \(K_1 \times (\partial K_2)\)
- Breakpoints lie on \((\partial K_1) \times (\partial K_2)\) (vertices of the product)
- Total of \(2k\) segments for a k-bounce trajectory

**Key theorem (Rudolf 2022, Theorem 4):** For 2D polygon factors, the optimal trajectory has at most 3 bounces. Since 3-bounce can degenerate to 2-bounce, we only enumerate 3-bounce combinatorics.

### 2.4 Reeb Flow on Lagrangian Products

On a segment where \(q\) moves and \(p\) is fixed on facet(s) of \(K_2\):
- Reeb vector: \(R = \frac{2}{h_j} \cdot (-n_j^{K_2})\) where \(n_j^{K_2}\) is the outward normal
- If \(p\) lies on a vertex (two facets \(j_1, j_2\)), velocity is a convex combination of the two Reeb vectors
- Segment time: \(t = h_{K_2}(q' - q)\) where \(h_{K_2}\) is the support function (equivalently, the \(K_2^\circ\)-norm)

Symmetrically for segments where \(p\) moves and \(q\) is fixed:
- Reeb vector: \(R = \frac{2}{h_i} \cdot (+n_i^{K_1})\)
- Segment time: \(t = h_{K_1}(p' - p)\)

The total action equals the sum of segment times.

### 2.5 Algorithm Steps

```rust
fn billiard_capacity(K: PolytopeHRep) -> Result<CapacityResult, Error> {
    // Step 1: Extract and validate 2D factors
    let (Kq, Kp) = extract_lagrangian_factors(K)?;
    let nq = Kq.num_facets;
    let np = Kp.num_facets;

    // Step 2: Enumerate all 3-bounce combinatorics
    // Each bounce alternates q-segment and p-segment
    // Combinatorics: which edge each of the 6 breakpoints lies on
    let mut best_action = f64::INFINITY;
    let mut best_orbit = None;

    for eq in all_triples(nq) {        // 3 edges in Kq
        for ep in all_triples(np) {    // 3 edges in Kp
            // Step 3: Setup LP for this combinatorics
            //
            // Variables (18 total):
            //   mq1, mq2, mq3 ∈ [0,1]  -- edge parameters in Kq
            //   mp1, mp2, mp3 ∈ [0,1]  -- edge parameters in Kp
            //   tq1, tq2, tq3 ∈ [0,∞)  -- times for q-segments
            //   tp1, tp2, tp3 ∈ [0,∞)  -- times for p-segments
            //   cq1, cq2, cq3 ∈ [0,1]  -- convex combo coeffs (if breakpoint on vertex)
            //   cp1, cp2, cp3 ∈ [0,1]  -- convex combo coeffs (if breakpoint on vertex)
            //
            // Derived points:
            //   q_k = Kq.vertices[eq_k] + mq_k * (Kq.vertices[eq_k+1] - Kq.vertices[eq_k])
            //   p_k = Kp.vertices[ep_k] + mp_k * (Kp.vertices[ep_k+1] - Kp.vertices[ep_k])
            //
            // Velocity constraints (Reeb flow):
            //   (q_{k+1} - q_k) / tq_k = convex_combo(Reeb vectors at p_k)
            //   (p_{k+1} - p_k) / tp_k = convex_combo(Reeb vectors at q_k)
            //
            // Objective: minimize T = tq1 + tp1 + tq2 + tp2 + tq3 + tp3

            let result = solve_billiard_lp(&Kq, &Kp, &eq, &ep);

            // Step 4: Filter degenerate solutions
            if let Some((action, orbit)) = result {
                if action < EPS_ZERO {
                    continue;  // point orbit, skip
                }
                if action < best_action {
                    best_action = action;
                    best_orbit = Some(orbit);
                }
            }
        }
    }

    Ok(CapacityResult {
        capacity: best_action,
        orbit: best_orbit,
        diagnostics: Diagnostics::default(),
    })
}
```

**Degeneracy handling:** Rather than filtering combinatorics upfront (e.g., excluding (1,1,2) but allowing (1,1,3)), we solve all LPs and discard solutions with action ≈ 0. This is simpler and catches all point-orbit degeneracies.

### 2.6 Implementation Details

**Lagrangian Factor Extraction:**
1. Partition facet normals by which coordinates are nonzero
2. Classify as "q-space only" (coords 0-1) or "p-space only" (coords 2-3)
3. Sort both q and p facets by `atan2(normal.y, normal.x)` to recover CCW boundary order
4. Build 2D polygons and track original 4D facet indices for orbit reconstruction

**Edge Index Convention:**
- Edge i connects vertex[i] to vertex[(i+1) mod n]
- Facet i has normal \(n_i\) and corresponds to edge i

**Orbit Reconstruction:**
Given LP solution (edge parameters mq, mp and segment times tq, tp):
1. Compute breakpoints: \(q_k = \text{interp}(\text{vertices}[eq_k], \text{vertices}[eq_k+1], mq_k)\)
2. Lift to 4D: breakpoints alternate between \((q_k, p_k)\) and \((q_k, p_{k+1})\)
3. Segment times come directly from the LP solution

### 2.7 Known Issues

1. **Pentagon bug (v0.1.0-archive):** Returned 2.127, expected 3.441 (HK-O 2024 Prop 1.4)
   - Root cause: Unknown, likely error in old LP formulation
   - The HK-O counterexample is Pentagon × RotatedPentagon

2. **Segment times (v0.1.0-archive):** Were placeholder zeros in old implementation
   - The new formulation in 2.5 computes times directly as LP variables

---

## 3. Algorithm: Tube (for General Polytopes)

> **Source:** Chaidez-Hutchings 2021, "Computing Reeb Dynamics on Polytopes"
> **Implementation status:** Returns NoValidOrbits on all tested polytopes
> **Thesis algorithm name:** Stoehler 2026

### 3.1 When to Use

Use for general polytopes, especially non-Lagrangian products.

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
                (action, orbit) = solve_closed_tube(ext)
                if action < best_action:
                    best_action = action
                    best_orbit = orbit
            else:  // Extension
                if ext.p_end not empty and ext.rotation <= 2 + \varepsilon:
                    worklist.push(ext)

    return CapacityResult { capacity: best_action, orbit: best_orbit }
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
4. Reconstruct 4D orbit point via barycentric interpolation

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

Works for ANY polytope, but \(O(F!)\) complexity limits to ~10 facets.

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
3. **Orbit reconstruction:** Converting billiard to full Reeb orbit requires more work

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
