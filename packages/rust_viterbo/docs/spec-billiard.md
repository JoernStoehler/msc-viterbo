# Developer Specification: Billiard Algorithm

> **Audience:** Claude Code agents implementing the Billiard algorithm
> **Prerequisite:** Read thesis chapter on algorithms; review HK2024 counterexample paper ([HK2024-counterexample.tex](../../../docs/papers/HK2024-counterexample/HK2024-counterexample.tex))
> **Status:** Draft specification for standalone crate
> **Reference Literature:** Rudolf 2022 "Minkowski billiards and symplectic capacities", Bezdek-Bezdek 2009 "Short billiard trajectories"

---

## Table of Contents

0. [Problem Statement](#0-problem-statement)
1. [Mathematical Background](#1-mathematical-background)
   - 1.1 Minkowski Billiards and EHZ Capacity
   - 1.2 The T°-Length (Dual Norm)
   - 1.3 Bounce Bound Theorem
   - 1.4 Billiard Trajectories as 4D Reeb Orbits
   - 1.5 Differential Inclusion Constraint
2. [Data Structures](#2-data-structures)
   - 2.1 Lagrangian Product Input
   - 2.2 2D Polygon Representation
   - 2.3 Edge and Vertex Data
   - 2.4 Trajectory Representation
   - 2.5 Result
3. [Algorithm](#3-algorithm)
   - 3.1 Overview
   - 3.2 Preprocessing: Extract Lagrangian Factors
   - 3.3 Edge Combination Enumeration
   - 3.4 Trajectory Parameterization
   - 3.5 Constrained Optimization per Edge Combination
   - 3.6 Action Computation
4. [Implementation Notes](#4-implementation-notes)
   - 4.1 Coordinate Conventions
   - 4.2 Handling Degenerate Cases
   - 4.3 Numerical Tolerances
   - 4.4 Complexity Analysis
5. [Test Cases](#5-test-cases)
   - 5.1 Ground Truth Values
   - 5.2 Capacity Axioms
   - 5.3 Algorithm Agreement
6. [Crate Structure](#6-crate-structure)
7. [References](#7-references)
8. [Open Questions](#8-open-questions)

---

## 0. Problem Statement

### What We Compute

**Input:** A Lagrangian product polytope \(K = K_q \times K_p \subset \mathbb{R}^2_q \times \mathbb{R}^2_p = \mathbb{R}^4\) where:
- \(K_q \subset \mathbb{R}^2_q\) is a convex polygon (the "billiard table" in configuration space)
- \(K_p \subset \mathbb{R}^2_p\) is a convex polygon (determines the "Minkowski metric" in momentum space)
- Both contain 0 in their interior

**Output:** The Ekeland-Hofer-Zehnder capacity \(c_{\text{EHZ}}(K_q \times K_p)\).

### Scope

This crate implements **capacity computation for Lagrangian products only**. It also reconstructs a minimum-action billiard trajectory (witness orbit).

### Why Billiard?

The Billiard algorithm:
- Works **only** for Lagrangian products (K₁ × K₂ with q/p separation)
- Exploits the billiard characterization: \(c_{\text{EHZ}}(K_q \times K_p)\) equals the minimum \(K_p^\circ\)-length among closed \(K_p\)-billiard trajectories in \(K_q\)
- Has polynomial complexity O(n³) where n = max(edges in K_q, edges in K_p)
- Provides the **most reliable** capacity computation for Lagrangian products

**Limitation:** Does not apply to non-Lagrangian products (use HK2017 or Tube algorithm instead).

---

## 1. Mathematical Background

### 1.1 Minkowski Billiards and EHZ Capacity

**Source:** Rudolf 2022 Theorem 4, Gutkin-Tabachnikov 2002

For a Lagrangian product \(K = K_q \times K_p\), the EHZ capacity has a billiard characterization:

\[
c_{\text{EHZ}}(K_q \times K_p) = \min \{ \|γ\|_{K_p^\circ} : γ \text{ is a closed } K_p\text{-billiard trajectory in } K_q \}
\]

where:
- \(K_p^\circ = \{y : \langle y, x \rangle \leq 1 \text{ for all } x \in K_p\}\) is the polar body of \(K_p\)
- \(\|v\|_{K_p^\circ} = h_{K_p}(v) = \max_{x \in K_p} \langle v, x \rangle\) is the \(K_p^\circ\)-length (support function of \(K_p\))
- A \(K_p\)-billiard trajectory follows the Minkowski reflection law determined by \(K_p\)

**Intuition:** The "table" is \(K_q\), and the "metric" (determining reflection angles and lengths) comes from \(K_p\).

### 1.2 Action via Reeb Vectors

The primary formulation uses Reeb vectors directly. For a q-segment where p lies on edge k of K_p:

**Reeb vector:** \(R_k = \frac{2}{h_{p,k}} J_{2D} n_{p,k}\)

**Displacement-time relation:**
- If p is in the **interior** of edge k: \(\Delta q = t \cdot R_k\) where \(t\) is the segment time
- If p is at a **vertex** (edges k₁, k₂ meet): \(\Delta q = \alpha R_{k_1} + \beta R_{k_2}\) where \(\alpha, \beta \geq 0\) and segment time \(t = \alpha + \beta\)

**Action = total time:**
\[
\text{Action} = \sum_{\text{segments}} t_i
\]

This is consistent with the general Reeb orbit framework: action equals the period of the closed characteristic.

**Equivalence to T°-length (literature formulation):**

The billiard literature (Rudolf 2022, HK2024) uses T°-length: \(\|v\|_{T^\circ} = h_T(v) = \max_{x \in T} \langle v, x \rangle\). The capacity equals the minimum T°-length of closed billiard trajectories. This is equivalent to the Reeb formulation via the relation between support functions and Reeb vectors.

### 1.3 Bounce Bound Theorem

**Source:** Bezdek-Bezdek 2009 (Lemma 2.1), Rudolf 2022 (Theorem 4)

**Theorem (Bezdek-Bezdek):** In \(\mathbb{R}^n\), every closed convex curve that cannot be translated into the interior of a convex body \(K\) can have vertices removed (preserving the non-translatability property) until it has at most \(n+1\) vertices.

**Corollary:** For 2D polygons (\(n = 2\)), the minimum-length closed billiard trajectory has at most **3 bounce points**.

**Implication for algorithm:** We only need to enumerate:
- 2-bounce trajectories
- 3-bounce trajectories

A k-bounce trajectory in the 4D Lagrangian product corresponds to 2k segments alternating between q-space motion and p-space motion.

### 1.4 Billiard Trajectories as 4D Reeb Orbits

A billiard trajectory in \(K_q\) with metric determined by \(K_p\) corresponds to a closed Reeb orbit on \(\partial(K_q \times K_p)\).

**4D structure of a k-bounce billiard:**
- The trajectory has 2k breakpoints in \(\mathbb{R}^4\)
- Segments alternate:
  - **q-segments:** Motion in \(\mathbb{R}^2_q\) while \(p\) is constant
  - **p-segments:** Motion in \(\mathbb{R}^2_p\) while \(q\) is constant

For a 3-bounce trajectory:
- 6 segments total: q₀→q₁, p₁→p₂, q₂→q₃, p₃→p₄, q₄→q₅, p₅→p₀ (closing)
- But since it's a billiard in \(K_q\), only 3 q-positions and 3 p-positions are distinct

**Breakpoint structure:**
```
Bounce 1: (q₁, p₁) where q₁ ∈ ∂K_q, p₁ ∈ interior or edge of K_p
Bounce 2: (q₂, p₂) where q₂ ∈ ∂K_q, p₂ ∈ interior or edge of K_p
Bounce 3: (q₃, p₃) where q₃ ∈ ∂K_q, p₃ ∈ interior or edge of K_p
```

### 1.5 Differential Inclusion Constraint

On a facet of \(K_q \times K_p\), the Reeb vector determines the allowed velocities.

**Reeb vector formula:**
\[
R_k = \frac{2}{h_k} J_{2D} n_k
\]
where \(h_k\) is the facet height and \(n_k\) is the outward unit normal, \(J_{2D} = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}\).

**Constraint verification (for q-segments, p on ∂K_p):**

| p location | Constraint | Time extraction |
|------------|------------|-----------------|
| Edge k interior | \(\Delta q = t \cdot R_k\) | \(t = \|\Delta q\| / \|R_k\|\) |
| Vertex (edges k₁, k₂) | \(\Delta q = \alpha R_{k_1} + \beta R_{k_2}\), \(\alpha,\beta \geq 0\) | \(t = \alpha + \beta\) |

**Symmetrically for p-segments** (q on ∂K_q): same formulas with q and p roles swapped.

```rust
/// Compute Reeb vector for motion in q-space when p is on edge k of K_p
fn reeb_vector_q(k_p: &Polygon2D, edge_idx: usize) -> Vector2<f64> {
    let n = k_p.normals[edge_idx];
    let h = k_p.heights[edge_idx];
    Vector2::new(-n[1], n[0]) * (2.0 / h)  // J_{2D} * n * (2/h)
}

/// Check if displacement is valid for edge interior (returns segment time if valid)
fn check_edge_constraint(delta: &Vector2<f64>, reeb: &Vector2<f64>, tol: f64) -> Option<f64> {
    let reeb_norm = reeb.norm();
    if reeb_norm < tol { return None; }

    // Check parallelism: delta × reeb ≈ 0
    let cross = delta[0] * reeb[1] - delta[1] * reeb[0];
    if cross.abs() > tol * reeb_norm { return None; }

    // Check same direction: delta · reeb > 0
    let dot = delta.dot(reeb);
    if dot < -tol { return None; }

    Some(dot / (reeb_norm * reeb_norm))  // t = (Δq · R) / |R|²
}

/// Check if displacement is in cone of two Reeb vectors (returns α, β if valid)
fn check_vertex_constraint(
    delta: &Vector2<f64>, r1: &Vector2<f64>, r2: &Vector2<f64>, tol: f64
) -> Option<(f64, f64)> {
    // Solve: delta = α·r1 + β·r2
    let det = r1[0] * r2[1] - r1[1] * r2[0];
    if det.abs() < tol { return None; }  // Degenerate (parallel Reeb vectors)

    let alpha = (delta[0] * r2[1] - delta[1] * r2[0]) / det;
    let beta = (r1[0] * delta[1] - r1[1] * delta[0]) / det;

    if alpha >= -tol && beta >= -tol {
        Some((alpha.max(0.0), beta.max(0.0)))
    } else {
        None
    }
}
```

---

## 2. Data Structures

### 2.1 Lagrangian Product Input

```rust
use nalgebra::{Vector4, Vector2};

/// A Lagrangian product K = K_q × K_p
pub struct LagrangianProduct {
    pub k_q: Polygon2D,  // Factor in q-space (the "billiard table")
    pub k_p: Polygon2D,  // Factor in p-space (determines the "metric")
}

impl LagrangianProduct {
    /// Convert to 4D H-representation
    pub fn to_hrep(&self) -> PolytopeHRep {
        let mut normals = Vec::new();
        let mut heights = Vec::new();

        // q-facets: normals of form (n_q, 0, 0)
        for i in 0..self.k_q.num_edges() {
            let n = self.k_q.normals[i];
            normals.push(Vector4::new(n[0], n[1], 0.0, 0.0));
            heights.push(self.k_q.heights[i]);
        }

        // p-facets: normals of form (0, 0, n_p)
        for i in 0..self.k_p.num_edges() {
            let n = self.k_p.normals[i];
            normals.push(Vector4::new(0.0, 0.0, n[0], n[1]));
            heights.push(self.k_p.heights[i]);
        }

        PolytopeHRep { normals, heights }
    }
}
```

### 2.2 2D Polygon Representation

```rust
/// A convex polygon in R² with 0 in its interior
/// Edges and vertices are in CCW order
pub struct Polygon2D {
    pub vertices: Vec<Vector2<f64>>,   // v[i] is vertex i, CCW order
    pub normals: Vec<Vector2<f64>>,    // n[i] is outward normal to edge i (from v[i] to v[i+1])
    pub heights: Vec<f64>,             // h[i] = ⟨n[i], v[i]⟩ > 0 (since 0 in interior)
}

impl Polygon2D {
    pub fn num_edges(&self) -> usize {
        self.vertices.len()
    }

    pub fn num_vertices(&self) -> usize {
        self.vertices.len()  // Same as num_edges for a polygon
    }

    /// Edge i goes from vertex i to vertex (i+1) mod n
    pub fn edge_start(&self, i: usize) -> Vector2<f64> {
        self.vertices[i]
    }

    pub fn edge_end(&self, i: usize) -> Vector2<f64> {
        self.vertices[(i + 1) % self.num_vertices()]
    }

    /// Point on edge i at parameter t ∈ [0, 1]
    /// t=0 gives vertex i, t=1 gives vertex i+1
    pub fn point_on_edge(&self, i: usize, t: f64) -> Vector2<f64> {
        let v0 = self.edge_start(i);
        let v1 = self.edge_end(i);
        v0 + (v1 - v0) * t
    }

    /// Validate polygon structure
    pub fn validate(&self) -> Result<(), String> {
        let n = self.num_vertices();
        if n < 3 {
            return Err("Polygon must have at least 3 vertices".to_string());
        }

        // Check normals are unit vectors
        for (i, normal) in self.normals.iter().enumerate() {
            if (normal.norm() - 1.0).abs() > EPS {
                return Err(format!("Normal {} is not unit: {}", i, normal.norm()));
            }
        }

        // Check heights are positive (0 in interior)
        for (i, &h) in self.heights.iter().enumerate() {
            if h <= EPS {
                return Err(format!("Height {} is not positive: {} (0 not in interior)", i, h));
            }
        }

        // Check CCW orientation (sum of cross products > 0)
        let mut signed_area = 0.0;
        for i in 0..n {
            let v0 = self.vertices[i];
            let v1 = self.vertices[(i + 1) % n];
            signed_area += v0[0] * v1[1] - v1[0] * v0[1];
        }
        if signed_area <= 0.0 {
            return Err("Vertices are not in CCW order".to_string());
        }

        Ok(())
    }
}
```

### 2.3 Edge and Vertex Data

For the billiard algorithm, we need to enumerate edge combinations:

```rust
/// An edge selection for a k-bounce trajectory
/// For 3 bounces: 3 edges from K_q and 3 edges from K_p
pub struct EdgeCombination {
    pub q_edges: Vec<usize>,  // Indices of edges in K_q (length = num_bounces)
    pub p_edges: Vec<usize>,  // Indices of edges in K_p (length = num_bounces)
}

/// A vertex of a polygon (meeting point of two edges)
pub struct VertexData {
    pub index: usize,           // Vertex index
    pub position: Vector2<f64>, // Vertex position
    pub edge_before: usize,     // Index of edge ending at this vertex
    pub edge_after: usize,      // Index of edge starting at this vertex
}
```

### 2.4 Trajectory Representation

```rust
/// A k-bounce billiard trajectory in q-space with p-positions
pub struct BilliardTrajectory {
    pub num_bounces: usize,

    /// Bounce points in q-space (on ∂K_q)
    pub q_positions: Vec<Vector2<f64>>,

    /// Corresponding p-positions (on ∂K_p or interior)
    pub p_positions: Vec<Vector2<f64>>,

    /// Edge indices in K_q where each q-position lies
    /// (or None if at a vertex)
    pub q_edges: Vec<Option<usize>>,

    /// Edge indices in K_p where each p-position lies
    /// (or None if at a vertex)
    pub p_edges: Vec<Option<usize>>,

    /// Total T°-length (= action)
    pub action: f64,
}

impl BilliardTrajectory {
    /// Convert to 4D Reeb orbit breakpoints
    pub fn to_4d_breakpoints(&self) -> Vec<Vector4<f64>> {
        let mut breakpoints = Vec::new();
        for i in 0..self.num_bounces {
            let q = self.q_positions[i];
            let p = self.p_positions[i];
            breakpoints.push(Vector4::new(q[0], q[1], p[0], p[1]));
        }
        breakpoints
    }
}
```

### 2.5 Result

```rust
/// Result of Billiard capacity computation
pub struct BilliardResult {
    /// The computed EHZ capacity
    pub capacity: f64,

    /// The optimal trajectory achieving the minimum
    pub witness: BilliardTrajectory,

    /// Number of edge combinations evaluated
    pub combinations_evaluated: usize,
}
```

---

## 3. Algorithm

### 3.1 Overview

```
Algorithm Billiard(K_q, K_p):
    Input: Lagrangian product K_q × K_p where K_q, K_p are 2D polygons
    Output: c_EHZ(K_q × K_p)

    1. Preprocess polygons (compute normals, heights, vertices)
    2. best_action = ∞
    3. For k = 2, 3:  // Number of bounces
        For each edge combination (e_q, e_p) with |e_q| = |e_p| = k:
            a. Parameterize trajectory by edge parameters
            b. Solve constrained optimization for minimum action
            c. If valid and action < best_action: update best
    4. Return capacity = best_action
```

### 3.2 Preprocessing: Extract Lagrangian Factors

Given a 4D polytope in H-rep, detect if it's a Lagrangian product and extract factors:

```rust
/// Check if a 4D polytope is a Lagrangian product and extract factors
pub fn extract_lagrangian_factors(hrep: &PolytopeHRep) -> Option<LagrangianProduct> {
    let mut q_normals = Vec::new();
    let mut q_heights = Vec::new();
    let mut p_normals = Vec::new();
    let mut p_heights = Vec::new();

    for (normal, &height) in hrep.normals.iter().zip(&hrep.heights) {
        let q_part = Vector2::new(normal[0], normal[1]);
        let p_part = Vector2::new(normal[2], normal[3]);

        let q_norm = q_part.norm();
        let p_norm = p_part.norm();

        if q_norm > EPS && p_norm < EPS {
            // q-facet
            q_normals.push(q_part / q_norm);
            q_heights.push(height / q_norm);
        } else if p_norm > EPS && q_norm < EPS {
            // p-facet
            p_normals.push(p_part / p_norm);
            p_heights.push(height / p_norm);
        } else {
            // Mixed facet - not a Lagrangian product
            return None;
        }
    }

    // Build polygons from facets (needs vertex computation)
    let k_q = polygon_from_facets(&q_normals, &q_heights)?;
    let k_p = polygon_from_facets(&p_normals, &p_heights)?;

    Some(LagrangianProduct { k_q, k_p })
}
```

### 3.3 Edge Combination Enumeration

For a k-bounce trajectory, we enumerate all ways to choose k edges from K_q and k edges from K_p:

```rust
use itertools::Itertools;

/// Generate all edge combinations for k bounces
fn edge_combinations(n_q: usize, n_p: usize, k: usize) -> Vec<EdgeCombination> {
    let q_choices: Vec<Vec<usize>> = (0..n_q).combinations_with_replacement(k).collect();
    let p_choices: Vec<Vec<usize>> = (0..n_p).combinations_with_replacement(k).collect();

    // Also need permutations of each choice
    let mut combinations = Vec::new();

    for q_subset in &q_choices {
        for q_perm in q_subset.iter().cloned().permutations(k) {
            for p_subset in &p_choices {
                for p_perm in p_subset.iter().cloned().permutations(k) {
                    combinations.push(EdgeCombination {
                        q_edges: q_perm.clone(),
                        p_edges: p_perm,
                    });
                }
            }
        }
    }

    combinations
}
```

**Note:** This generates many redundant combinations. For efficiency:
- Use symmetry: cyclic rotations of a trajectory are equivalent
- Prune obviously infeasible combinations (e.g., same edge repeated without valid vertex transition)

### 3.4 Trajectory Parameterization

A k-bounce trajectory is parameterized by 2k parameters:
- \(t_{q,i} \in [0, 1]\): position on edge \(e_{q,i}\) of K_q for bounce i
- \(t_{p,i} \in [0, 1]\): position on edge \(e_{p,i}\) of K_p for bounce i

The trajectory's breakpoints are:
```rust
q_i = K_q.point_on_edge(e_q[i], t_q[i])
p_i = K_p.point_on_edge(e_p[i], t_p[i])
```

**Closure constraint:** The trajectory must close:
\[
\sum_{i=0}^{k-1} (q_{i+1} - q_i) = 0 \quad \text{and} \quad \sum_{i=0}^{k-1} (p_{i+1} - p_i) = 0
\]
(with indices mod k)

### 3.5 Constrained Optimization per Edge Combination

For a fixed edge combination, we solve for the parameters that:
1. Satisfy the closure constraint
2. Satisfy the differential inclusion (Reeb velocity constraint)
3. Minimize the action

**Variables:** \((t_{q,0}, \ldots, t_{q,k-1}, t_{p,0}, \ldots, t_{p,k-1}) \in [0,1]^{2k}\)

**Constraints:**

1. **Closure in q-space:**
\[
\sum_{i=0}^{k-1} (q_{i+1 \mod k} - q_i) = 0
\]

2. **Closure in p-space:**
\[
\sum_{i=0}^{k-1} (p_{i+1 \mod k} - p_i) = 0
\]

3. **Differential inclusion:** For each segment, the velocity direction must be compatible with the Reeb flow. This is automatically satisfied when we use the T°-length formulation (the billiard dynamics encode the Reeb constraint).

**Objective:** Minimize action
\[
A = \sum_{i=0}^{k-1} \|q_{i+1} - q_i\|_{K_p^\circ}
\]

**Note:** The p-displacement contributes to "time" but not directly to "action" in the billiard formulation. The T°-length of the q-displacement gives the action.

```rust
/// Solve for minimum action trajectory with given edge combination
fn solve_billiard_lp(
    k_q: &Polygon2D,
    k_p: &Polygon2D,
    combo: &EdgeCombination,
) -> Option<(f64, BilliardTrajectory)> {
    let k = combo.q_edges.len();

    // For k=2 or k=3, we can solve analytically or use simple LP
    // The constraints are linear in the edge parameters
    // The objective (T°-length) is piecewise linear

    // Simplified approach: discretize and search
    // (A complete implementation would use proper LP with piecewise linear objective)

    // ... implementation details ...

    unimplemented!()
}
```

### 3.6 Action Computation

The action of a billiard trajectory equals its \(K_p^\circ\)-length:

```rust
fn compute_action(
    trajectory: &BilliardTrajectory,
    k_p: &Polygon2D,
) -> f64 {
    let mut action = 0.0;
    let k = trajectory.num_bounces;

    for i in 0..k {
        let q_i = trajectory.q_positions[i];
        let q_next = trajectory.q_positions[(i + 1) % k];
        let displacement = q_next - q_i;

        // T°-length = support function of K_p
        action += t_dual_length(&displacement, &k_p.vertices);
    }

    action
}
```

---

## 4. Implementation Notes

### 4.1 Coordinate Conventions

We use the standard symplectic coordinates:
- \(\mathbb{R}^4 = (q_1, q_2, p_1, p_2)\)
- \(K_q \subset \mathbb{R}^2\) with coordinates \((q_1, q_2)\)
- \(K_p \subset \mathbb{R}^2\) with coordinates \((p_1, p_2)\)

The 4D standard complex structure:
\[
J(q_1, q_2, p_1, p_2) = (-p_1, -p_2, q_1, q_2)
\]

For 2D within a Lagrangian factor:
\[
J_{2D}(x, y) = (-y, x) \quad \text{(90° CCW rotation)}
\]

### 4.2 Handling Degenerate Cases

**Bounces at vertices:**
When a bounce point lies at a vertex of K_q (intersection of two edges), the "edge" assignment is ambiguous. Handle by:
1. Detecting when t ≈ 0 or t ≈ 1 (within tolerance)
2. Allowing the velocity to be a convex combination of the two edge velocities

**Zero-length trajectories:**
Trajectories where all bounce points coincide (action = 0) are not physical Reeb orbits. Discard solutions with action < EPS.

**Collinear bounce points:**
If all k bounce points are collinear, this reduces to a 2-bounce trajectory. Handle by checking if intermediate bounces are on the line segment.

### 4.3 Numerical Tolerances

```rust
/// Tolerance for comparing floating point values
const EPS: f64 = 1e-10;

/// Tolerance for constraint satisfaction
const CONSTRAINT_TOL: f64 = 1e-8;

/// Tolerance for edge parameter bounds (allow slight overshoot)
const EDGE_PARAM_TOL: f64 = 1e-9;

/// Minimum action to consider (below this is "zero length")
const MIN_ACTION: f64 = 1e-8;
```

### 4.4 Complexity Analysis

| Component | Complexity |
|-----------|------------|
| 2-bounce combinations | O(n_q² × n_p²) |
| 3-bounce combinations | O(n_q³ × n_p³) |
| Solve per combination | O(1) with direct formula, O(poly) with LP |
| Total | O((n_q × n_p)³) |

For typical polygons (5-20 edges), this is very fast (< 1ms).

---

## 5. Test Cases

### 5.1 Ground Truth Values

| Polytope | c_EHZ | Source | Notes |
|----------|-------|--------|-------|
| Tesseract [-1,1]⁴ | 4.0 | HK2017 Ex 4.6 | Square × Square |
| Rectangle 2×1 × Rectangle 2×1 | 1.0 | Scaling | |
| Pentagon × RotatedPentagon(90°) | 3.441 | HK-O 2024 Prop 1 | Counterexample |
| Triangle × Triangle (circumradius 1) | 1.5 | [NEEDS CITATION] | |
| Simplex_q × Simplex_p | [NEEDS CITATION] | | |

**Pentagon × RotatedPentagon details:**

From HK-O 2024:
- \(K\) = regular pentagon with vertices at \((\cos(2\pi k/5), \sin(2\pi k/5))\)
- \(T\) = K rotated by 90°
- \(c_{\text{EHZ}} = 2 \cos(\pi/10)(1 + \cos(\pi/5)) \approx 3.441\)

**Important:** Both 2-bounce and 3-bounce searches should find this minimum. The HK2024 proof (line 300) shows that certain 3-bounce trajectories with x₂ at vertex v₄ achieve exactly the same action as 2-bounce diagonals. This validates both code paths.

```rust
#[test]
fn test_pentagon_counterexample() {
    let k = regular_pentagon();  // circumradius 1
    let t = rotate_polygon(&k, PI / 2.0);  // 90° rotation

    let expected = 2.0 * (PI / 10.0).cos() * (1.0 + (PI / 5.0).cos());

    // Test full algorithm
    let result = billiard_capacity(&k, &t);
    assert!((result.capacity - expected).abs() < 1e-6,
        "Pentagon capacity: expected {}, got {}", expected, result.capacity);

    // Test that both bounce classes find the minimum
    let result_2bounce = billiard_capacity_k_bounce(&k, &t, 2);
    let result_3bounce = billiard_capacity_k_bounce(&k, &t, 3);

    assert!((result_2bounce.capacity - expected).abs() < 1e-6,
        "2-bounce should find minimum");
    assert!((result_3bounce.capacity - expected).abs() < 1e-6,
        "3-bounce should find minimum (HK2024 proof line 300)");
}
```

### 5.2 Capacity Axioms

```rust
#[test]
fn test_scaling_axiom() {
    // c(λK_q × λK_p) = λ² c(K_q × K_p)
    let k_q = some_polygon();
    let k_p = some_polygon();
    let lambda = 2.0;

    let c_original = billiard_capacity(&k_q, &k_p).capacity;
    let c_scaled = billiard_capacity(
        &scale_polygon(&k_q, lambda),
        &scale_polygon(&k_p, lambda)
    ).capacity;

    assert!((c_scaled - lambda * lambda * c_original).abs() < 1e-6);
}

#[test]
fn test_translation_invariance() {
    // Translating both factors doesn't change capacity
    // (as long as 0 stays in interior)
    let k_q = some_polygon();
    let k_p = some_polygon();

    let c_original = billiard_capacity(&k_q, &k_p).capacity;

    // Small translation
    let v = Vector2::new(0.1, 0.1);
    let c_translated = billiard_capacity(
        &translate_polygon(&k_q, &v),
        &translate_polygon(&k_p, &v)
    ).capacity;

    assert!((c_original - c_translated).abs() < 1e-6);
}
```

### 5.3 Algorithm Agreement

```rust
#[test]
fn test_billiard_vs_hk2017() {
    // For Lagrangian products, both algorithms should agree
    let k_q = random_polygon(5);
    let k_p = random_polygon(5);

    let product = LagrangianProduct { k_q: k_q.clone(), k_p: k_p.clone() };
    let hrep = product.to_hrep();

    let c_billiard = billiard_capacity(&k_q, &k_p).capacity;
    let c_hk2017 = hk2017_capacity(&hrep).capacity;

    let rel_error = (c_billiard - c_hk2017).abs() / c_billiard;
    assert!(rel_error < 0.01,
        "Algorithms disagree: billiard={}, hk2017={}", c_billiard, c_hk2017);
}
```

### 5.4 Witness Validation Tests

The witness trajectory must satisfy geometric constraints. These tests catch bugs where the capacity value is correct but the witness is invalid.

```rust
/// Validate that a witness trajectory satisfies all constraints
fn validate_witness(
    witness: &BilliardTrajectory,
    k_q: &Polygon2D,
    k_p: &Polygon2D,
    tol: f64,
) -> Result<(), String> {
    let k = witness.num_bounces;

    // 1. Closure: sum of displacements = 0
    let mut q_sum = Vector2::zeros();
    let mut p_sum = Vector2::zeros();
    for i in 0..k {
        q_sum += witness.q_positions[(i + 1) % k] - witness.q_positions[i];
        p_sum += witness.p_positions[(i + 1) % k] - witness.p_positions[i];
    }
    if q_sum.norm() > tol {
        return Err(format!("q-closure violated: sum = {:?}", q_sum));
    }
    if p_sum.norm() > tol {
        return Err(format!("p-closure violated: sum = {:?}", p_sum));
    }

    // 2. Boundary: q_i ∈ ∂K_q, p_i ∈ ∂K_p (or interior for generalized bounces)
    for (i, q) in witness.q_positions.iter().enumerate() {
        if !is_on_boundary_or_interior(q, k_q, tol) {
            return Err(format!("q[{}] = {:?} not on ∂K_q", i, q));
        }
    }
    for (i, p) in witness.p_positions.iter().enumerate() {
        if !is_on_boundary_or_interior(p, k_p, tol) {
            return Err(format!("p[{}] = {:?} not on ∂K_p", i, p));
        }
    }

    // 3. Reeb constraint: Δq in cone(R) for each segment
    let mut computed_action = 0.0;
    for i in 0..k {
        let delta_q = witness.q_positions[(i + 1) % k] - witness.q_positions[i];
        let p_pos = witness.p_positions[i];

        let segment_time = match classify_boundary_point(&p_pos, k_p, tol) {
            BoundaryLocation::EdgeInterior(edge_idx) => {
                let reeb = reeb_vector_q(k_p, edge_idx);
                check_edge_constraint(&delta_q, &reeb, tol)
                    .ok_or(format!("Segment {}: Δq not parallel to Reeb", i))?
            }
            BoundaryLocation::Vertex(e1, e2) => {
                let r1 = reeb_vector_q(k_p, e1);
                let r2 = reeb_vector_q(k_p, e2);
                let (alpha, beta) = check_vertex_constraint(&delta_q, &r1, &r2, tol)
                    .ok_or(format!("Segment {}: Δq not in Reeb cone", i))?;
                alpha + beta
            }
            BoundaryLocation::Interior => {
                return Err(format!("p[{}] in interior, not on boundary", i));
            }
        };
        computed_action += segment_time;
    }

    // 4. Action consistency: computed action ≈ returned capacity
    if (computed_action - witness.action).abs() > tol {
        return Err(format!(
            "Action mismatch: computed {} vs returned {}",
            computed_action, witness.action
        ));
    }

    Ok(())
}

#[test]
fn test_witness_validity() {
    for _ in 0..100 {
        let k_q = random_polygon(5);
        let k_p = random_polygon(5);

        let result = billiard_capacity(&k_q, &k_p);
        validate_witness(&result.witness, &k_q, &k_p, CONSTRAINT_TOL)
            .expect("Witness should be valid");
    }
}

#[test]
fn test_pentagon_witness_validity() {
    let k = regular_pentagon();
    let t = rotate_polygon(&k, PI / 2.0);

    let result = billiard_capacity(&k, &t);
    validate_witness(&result.witness, &k, &t, CONSTRAINT_TOL)
        .expect("Pentagon witness should be valid");

    // Additionally verify it's a 2-bounce or valid 3-bounce
    assert!(result.witness.num_bounces == 2 || result.witness.num_bounces == 3);
}
```

---

## 6. Crate Structure

```
packages/rust_viterbo/billiard/
├── Cargo.toml
├── src/
│   ├── lib.rs           # Public API
│   ├── types.rs         # Data structures (Polygon2D, LagrangianProduct, etc.)
│   ├── polygon.rs       # 2D polygon operations
│   ├── extract.rs       # Extract Lagrangian factors from 4D polytope
│   ├── enumerate.rs     # Edge combination enumeration
│   ├── solve.rs         # Constrained optimization per combination
│   ├── action.rs        # T°-length computation
│   └── algorithm.rs     # Main billiard_capacity function
└── tests/
    ├── ground_truth.rs  # Known capacity values
    ├── axioms.rs        # Capacity axioms
    └── agreement.rs     # Algorithm agreement tests
```

**Cargo.toml:**

```toml
[package]
name = "billiard"
version = "0.1.0"
edition = "2021"

[dependencies]
nalgebra = "0.32"
itertools = "0.12"

[dev-dependencies]
approx = "0.5"
proptest = "1.0"
```

**Public API (lib.rs):**

```rust
pub mod types;
pub mod polygon;
pub mod extract;
pub mod enumerate;
pub mod solve;
pub mod action;
pub mod algorithm;

pub use types::{Polygon2D, LagrangianProduct, BilliardTrajectory, BilliardResult};
pub use extract::extract_lagrangian_factors;
pub use algorithm::billiard_capacity;
```

---

## 7. References

### Primary Sources

- **Rudolf 2022:** Rudolf, D. "Minkowski billiards and symplectic capacities." *Journal of Modern Dynamics* 17 (2021): 189-216. arXiv:2203.01718.
- **Bezdek-Bezdek 2009:** Bezdek, K. and Bezdek, D. "Short billiard trajectories." *Geom. Dedicata* 141 (2009): 197-206.
- **Gutkin-Tabachnikov 2002:** Gutkin, E. and Tabachnikov, S. "Billiards in Finsler and Minkowski geometries." *Journal of Geometry and Physics* 40 (2002): 277-301.

### Application / Ground Truth

- **HK-O 2024:** Haim-Kislev, P. and Ostrover, Y. "A Counterexample to Viterbo's Conjecture." arXiv:2405.16513.
- **HK2017:** Haim-Kislev, P. "On the Symplectic Size of Convex Polytopes." arXiv:1712.03494.

### Related

- **Artstein-Avidan-Ostrover 2014:** "Bounds for Minkowski billiard trajectories in convex bodies." IMRN 2014: 165-193.

---

## 8. Open Questions

### 8.1 Billiard-to-Reeb Orbit Mapping

A k-bounce billiard corresponds to a 2k-segment Reeb orbit alternating between q-facets and p-facets. The exact mapping of segment times to T°-lengths should be derived when implementing witness orbit reconstruction.

### 8.2 Degenerate Polygons

Input polygons with collinear vertices or 0 on the boundary should be rejected during validation.

### 8.3 Higher Dimensions

The billiard characterization extends to \(\mathbb{R}^{2n}\) for n > 2 (Rudolf 2022 Theorem 4). The bounce bound becomes n+1 (Bezdek-Bezdek Lemma 2.1), making enumeration O(edges^{n+1}).
