# Developer Specification: Billiard Algorithm

> **Audience:** Claude Code agents implementing the Billiard algorithm
> **Prerequisite:** Read thesis chapter on algorithms; review HK2024 counterexample paper ([HK2024-counterexample.tex](../../../docs/papers/HK2024-counterexample/HK2024-counterexample.tex))
> **Status:** Draft specification for standalone crate
> **Reference Literature:** Rudolf 2021 "Minkowski billiards and symplectic capacities" (JMD vol. 17), Bezdek-Bezdek 2009 "Short billiard trajectories"

---

## Table of Contents

0. [Problem Statement](#0-problem-statement)
1. [Mathematical Background](#1-mathematical-background)
   - 1.1 Minkowski Billiards and EHZ Capacity
   - 1.2 Action via Reeb Vectors
   - 1.3 Bounce Bound Theorem
   - 1.4 Billiard Trajectories as 4D Reeb Orbits
   - 1.5 Piecewise Linear Structure of the Action Function
   - 1.6 Differential Inclusion Constraint
2. [Data Structures](#2-data-structures)
   - 2.1 Lagrangian Product Input
   - 2.2 2D Polygon Representation
   - 2.3 Edge and Vertex Data
   - 2.4 Trajectory Representation
   - 2.5 Result
   - 2.6 Helper Functions
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
   - 5.4 Witness Validation Tests
   - 5.5 Vertex Optimality Tests
   - 5.6 Input Validation Tests
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

**Source:** Rudolf 2021 (JMD vol. 17), Gutkin-Tabachnikov 2002

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

The primary formulation uses Reeb vectors directly.

**4D Reeb vector formula:** On a facet of a 4D polytope with outward unit normal \(n \in \mathbb{R}^4\) and height \(h\), the Reeb vector is:
\[
R = \frac{2}{h} J n \quad \text{where } J = \begin{pmatrix} 0 & -I_2 \\ I_2 & 0 \end{pmatrix}
\]

For \(n = (n_q, n_p)\) with \(n_q, n_p \in \mathbb{R}^2\), this gives \(R = \frac{2}{h}(-n_p, n_q)\).

**Projection to Lagrangian products:** For \(K = K_q \times K_p\), facets are either:
- **p-facets** (full \(K_q\) × edge of \(K_p\)): normal \(n = (0, n_p)\) where \(n_p\) is the 2D outward normal of the p-edge
  - Reeb vector: \(R = \frac{2}{h}(-n_p, 0)\), so motion is **only in q-space** with direction \(-n_p\)
- **q-facets** (edge of \(K_q\) × full \(K_p\)): normal \(n = (n_q, 0)\) where \(n_q\) is the 2D outward normal of the q-edge
  - Reeb vector: \(R = \frac{2}{h}(0, n_q)\), so motion is **only in p-space** with direction \(+n_q\)

This explains the billiard structure: trajectories alternate between q-motion (when on a p-facet) and p-motion (when on a q-facet).

**Displacement-time relation for q-segments** (p on edge k of \(K_p\), with 2D normal \(n_{p,k}\) and height \(h_{p,k}\)):

Let \(V_k = -\frac{2}{h_{p,k}} n_{p,k}\) be the q-velocity direction (the q-component of the Reeb vector).

- If p is in the **interior** of edge k: \(\Delta q = t \cdot V_k\) where \(t \geq 0\) is the segment time
- If p is at a **vertex** (edges k₁, k₂ meet): \(\Delta q = \alpha V_{k_1} + \beta V_{k_2}\) where \(\alpha, \beta \geq 0\) and segment time \(t = \alpha + \beta\)

**Action = total time:**
\[
\text{Action} = \sum_{\text{segments}} t_i
\]

This is consistent with the general Reeb orbit framework: action equals the period of the closed characteristic.

**Equivalence to T°-length (literature formulation):**

The billiard literature (Rudolf 2021, HK2024) uses T°-length: \(\|v\|_{T^\circ} = h_T(v) = \max_{x \in T} \langle v, x \rangle\). The capacity equals the minimum T°-length of closed billiard trajectories. This is equivalent to the Reeb formulation via the relation between support functions and Reeb vectors.

### 1.3 Bounce Bound Theorem

**Source:** Bezdek-Bezdek 2009 (Lemma 2.1, Lemma 2.4), Rudolf 2021

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

### 1.5 Piecewise Linear Structure of the Action Function

**Mathematical Claim:** The action function is piecewise linear and convex in the trajectory parameters.

**Proof:**
1. The action is \(A = \sum_{i} \|q_{i+1} - q_i\|_{K_p^\circ}\)
2. Each term \(\|v\|_{K_p^\circ} = h_{K_p}(v) = \max_{w \in \text{vertices}(K_p)} \langle v, w \rangle\)
3. This is a maximum of linear functions in \(v\), hence **convex and piecewise linear**
4. Since \(q_i = \text{point\_on\_edge}(e_i, t_i)\) is **linear** in the edge parameter \(t_i\), the displacements \(\Delta q_i = q_{i+1} - q_i\) are linear in the parameters
5. Composing: \(\|\Delta q_i\|_{K_p^\circ}\) is piecewise linear convex in the parameters
6. Sum of convex functions is convex, sum of piecewise linear functions is piecewise linear

**Consequence (Vertex Optimality Theorem):** The minimum of a piecewise linear convex function over a polytope is attained at a vertex of the feasible polytope.

**Source:** This is a standard result in convex optimization. See Boyd & Vandenberghe "Convex Optimization" §4.1.3, or note that piecewise linear convex functions have linear pieces, and on each piece the minimum over a polytope is at a vertex; the global minimum is the minimum over finitely many vertices.

**Algorithmic Implication:** To find the minimum action for a fixed edge combination:
1. Build the feasible polytope (closure constraints + box constraints)
2. Enumerate vertices of this polytope (finite set)
3. Evaluate action at each vertex
4. Return the minimum

This is **exact** (no approximation) and runs in polynomial time for fixed bounce count k.

### 1.6 Differential Inclusion Constraint

On a facet of \(K_q \times K_p\), the Reeb vector determines the allowed velocities. See §1.2 for the derivation from the 4D symplectic structure.

**Summary for q-segments** (p on edge k of \(K_p\), with 2D outward normal \(n_{p,k}\) and height \(h_{p,k}\)):

The q-velocity direction is \(V_k = -\frac{2}{h_{p,k}} n_{p,k}\) (opposite to the p-edge normal, scaled).

| p location | Constraint | Time extraction |
|------------|------------|-----------------|
| Edge k interior | \(\Delta q = t \cdot V_k\) | \(t = \|\Delta q\| / \|V_k\|\) |
| Vertex (edges k₁, k₂) | \(\Delta q = \alpha V_{k_1} + \beta V_{k_2}\), \(\alpha,\beta \geq 0\) | \(t = \alpha + \beta\) |

**Symmetrically for p-segments** (q on edge j of \(K_q\), with 2D outward normal \(n_{q,j}\) and height \(h_{q,j}\)):

The p-velocity direction is \(W_j = +\frac{2}{h_{q,j}} n_{q,j}\) (same direction as the q-edge normal, scaled).

```rust
/// Compute velocity direction for q-motion when p is on edge k of K_p.
/// This is the q-component of the 4D Reeb vector: V_k = -(2/h_k) * n_k
fn q_velocity(k_p: &Polygon2D, edge_idx: usize) -> Vector2<f64> {
    let n = k_p.normals[edge_idx];  // 2D outward normal of p-edge
    let h = k_p.heights[edge_idx];
    -n * (2.0 / h)
}

/// Compute velocity direction for p-motion when q is on edge j of K_q.
/// This is the p-component of the 4D Reeb vector: W_j = +(2/h_j) * n_j
fn p_velocity(k_q: &Polygon2D, edge_idx: usize) -> Vector2<f64> {
    let n = k_q.normals[edge_idx];  // 2D outward normal of q-edge
    let h = k_q.heights[edge_idx];
    n * (2.0 / h)
}

/// Check if displacement is valid for edge interior (returns segment time if valid)
fn check_edge_constraint(delta: &Vector2<f64>, velocity: &Vector2<f64>, tol: f64) -> Option<f64> {
    let v_norm = velocity.norm();
    if v_norm < tol { return None; }

    // Check parallelism: delta × velocity ≈ 0
    let cross = delta[0] * velocity[1] - delta[1] * velocity[0];
    if cross.abs() > tol * v_norm { return None; }

    // Check same direction: delta · velocity > 0
    let dot = delta.dot(velocity);
    if dot < -tol { return None; }

    Some(dot / (v_norm * v_norm))  // t = (Δ · V) / |V|²
}

/// Check if displacement is in cone of two velocity vectors (returns α, β if valid)
fn check_vertex_constraint(
    delta: &Vector2<f64>, v1: &Vector2<f64>, v2: &Vector2<f64>, tol: f64
) -> Option<(f64, f64)> {
    // Solve: delta = α·v1 + β·v2
    let det = v1[0] * v2[1] - v1[1] * v2[0];
    if det.abs() < tol { return None; }  // Degenerate (parallel velocity vectors)

    let alpha = (delta[0] * v2[1] - delta[1] * v2[0]) / det;
    let beta = (v1[0] * delta[1] - v1[1] * delta[0]) / det;

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

### 2.6 Helper Functions

These functions are used throughout the algorithm but defined here for reference:

```rust
/// Compute T°-length (support function) of a displacement vector
/// h_T(v) = max_{x ∈ T} ⟨v, x⟩ = max over vertices
fn t_dual_length(v: &Vector2<f64>, t_vertices: &[Vector2<f64>]) -> f64 {
    t_vertices.iter()
        .map(|w| v.dot(w))
        .fold(f64::NEG_INFINITY, f64::max)
}

/// Build a 2D polygon from H-representation (normals and heights)
/// Returns None if the constraints don't form a bounded polygon
fn polygon_from_facets(
    normals: &[Vector2<f64>],
    heights: &[f64],
) -> Option<Polygon2D> {
    // 1. Compute vertices by intersecting adjacent half-planes
    // 2. Sort vertices in CCW order
    // 3. Build Polygon2D structure
    //
    // Implementation: For each pair of consecutive edges (i, i+1 mod n),
    // solve the 2x2 system: ⟨n_i, x⟩ = h_i and ⟨n_{i+1}, x⟩ = h_{i+1}
    // to find the vertex at their intersection.

    let n = normals.len();
    if n < 3 { return None; }

    let mut vertices = Vec::with_capacity(n);
    for i in 0..n {
        let j = (i + 1) % n;
        // Solve: n_i · x = h_i, n_j · x = h_j
        let det = normals[i][0] * normals[j][1] - normals[i][1] * normals[j][0];
        if det.abs() < EPS { return None; }  // Parallel edges

        let x = (heights[i] * normals[j][1] - heights[j] * normals[i][1]) / det;
        let y = (normals[i][0] * heights[j] - normals[j][0] * heights[i]) / det;
        vertices.push(Vector2::new(x, y));
    }

    Some(Polygon2D {
        vertices,
        normals: normals.to_vec(),
        heights: heights.to_vec(),
    })
}

/// Classify where a point lies on a polygon boundary
enum BoundaryLocation {
    EdgeInterior(usize),      // On edge i, not at a vertex
    Vertex(usize, usize),     // At vertex between edges i and j
    Interior,                 // Inside the polygon (not on boundary)
    Exterior,                 // Outside the polygon
}

fn classify_boundary_point(
    point: &Vector2<f64>,
    polygon: &Polygon2D,
    tol: f64,
) -> BoundaryLocation {
    let n = polygon.num_edges();

    // Check distance to each edge
    for i in 0..n {
        let dist_to_edge = polygon.normals[i].dot(point) - polygon.heights[i];

        if dist_to_edge.abs() < tol {
            // Point is on edge i's supporting line
            // Check if it's at a vertex (also close to adjacent edge)
            let prev = (i + n - 1) % n;
            let dist_to_prev = polygon.normals[prev].dot(point) - polygon.heights[prev];

            if dist_to_prev.abs() < tol {
                return BoundaryLocation::Vertex(prev, i);
            }
            return BoundaryLocation::EdgeInterior(i);
        }

        if dist_to_edge > tol {
            return BoundaryLocation::Exterior;
        }
    }

    BoundaryLocation::Interior
}

/// Check if point is on boundary or interior of polygon
fn is_on_boundary_or_interior(
    point: &Vector2<f64>,
    polygon: &Polygon2D,
    tol: f64,
) -> bool {
    !matches!(
        classify_boundary_point(point, polygon, tol),
        BoundaryLocation::Exterior
    )
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

For a k-bounce trajectory, we enumerate all ordered k-tuples of edges from K_q and K_p independently:

```rust
/// Generate all edge combinations for k bounces
/// Returns n_q^k × n_p^k combinations
fn edge_combinations(n_q: usize, n_p: usize, k: usize) -> Vec<EdgeCombination> {
    let mut combinations = Vec::new();

    // Enumerate all ordered k-tuples for q-edges and p-edges independently
    for q_edges in ordered_tuples(n_q, k) {
        for p_edges in ordered_tuples(n_p, k) {
            combinations.push(EdgeCombination { q_edges, p_edges });
        }
    }

    combinations
}

/// Generate all ordered k-tuples from {0, ..., n-1}
/// Allows repetition (same edge can appear multiple times)
fn ordered_tuples(n: usize, k: usize) -> impl Iterator<Item = Vec<usize>> {
    // For k=2: (0..n).flat_map(|i| (0..n).map(move |j| vec![i, j]))
    // For k=3: nested iteration over i, j, k
    //
    // Using itertools::iproduct! for clarity:
    match k {
        2 => iproduct!(0..n, 0..n)
            .map(|(a, b)| vec![a, b])
            .collect::<Vec<_>>()
            .into_iter(),
        3 => iproduct!(0..n, 0..n, 0..n)
            .map(|(a, b, c)| vec![a, b, c])
            .collect::<Vec<_>>()
            .into_iter(),
        _ => panic!("Only k=2,3 supported"),
    }
}
```

**Complexity:**
- k=2: n_q² × n_p² edge combinations
- k=3: n_q³ × n_p³ edge combinations

For a pentagon (n=5): 5³ × 5³ = 15,625 combinations for 3-bounce. Fast enough.

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

3. **Differential inclusion:** For each segment, the velocity direction must be compatible with the Reeb flow:
   - **q-motion segments** (p on ∂K_p): q̇ must be in the cone of velocity directions V_k = -(2/h_k)n_k for active p-edges. This determines where p must be on ∂K_p given the q-displacement direction.
   - **p-motion segments** (q on ∂K_q): ṗ must be in the cone of velocity directions W_k = (2/h_k)n_k for active q-edges. This must be **explicitly validated** for each p-transition at a bounce point.

   **Warning:** It is NOT sufficient to only check q-displacement achievability. The p-transitions at each bounce must also be validated. See `findings-orbit-validation-2026-01-26.md` for details on this subtle issue.

**Objective:** Minimize action
\[
A = \sum_{i=0}^{k-1} \|q_{i+1} - q_i\|_{K_p^\circ}
\]

**Note:** The p-displacement contributes to "time" but not directly to "action" in the billiard formulation. The T°-length of the q-displacement gives the action.

**Solution approach for k=2 (2-bounce):**

For 2-bounce trajectories, the problem simplifies significantly:
- Variables: \(t_{q,0}, t_{q,1}, t_{p,0}, t_{p,1} \in [0,1]\)
- Closure: \(q_1 - q_0 + q_0 - q_1 = 0\) (automatically satisfied for 2-bounce back-and-forth)
- The trajectory goes \(q_0 \to q_1 \to q_0\) in q-space

**Why vertex enumeration is correct (per Section 1.5):**
1. The feasible region is a subset of the 4D box \([0,1]^4\) (not all corners yield valid orbits)
2. The action function is piecewise linear convex in the parameters
3. By the **Vertex Optimality Theorem** (Section 1.5), the minimum is at a vertex
4. Vertices of the box are the 16 points with \(t_i \in \{0, 1\}\), but **not all are feasible**

Therefore, checking all corner combinations and filtering for valid orbits is **exact**, not an approximation.

**Validation required for each candidate:**
1. q-displacement achievability (determines p position during q-motion)
2. p-transition achievability at each bounce (p must be able to move between required positions)

**Solution approach for k=3 (3-bounce):**

For 3-bounce trajectories:
1. Fix the edge combination \((e_{q,0}, e_{q,1}, e_{q,2})\) and \((e_{p,0}, e_{p,1}, e_{p,2})\)
2. Parameterize: \(q_i = K_q.\text{point\_on\_edge}(e_{q,i}, t_{q,i})\)
3. Closure constraint gives 2 linear equations (in 2D) for q and 2 for p
4. With 6 variables and 4 linear constraints, we have a 2D feasible region
5. **By Section 1.5**, the minimum is at a vertex of this polytope
6. Enumerate vertices and evaluate action at each

**Feasible polytope structure:**
- Start with box \([0,1]^6\) (6 parameters)
- Add closure constraints: \(A_q \cdot t_q = b_q\) (2 equations), \(A_p \cdot t_p = b_p\) (2 equations)
- Result: intersection of a 2D affine subspace with the 6D box
- This is a convex polytope, possibly empty (infeasible combination)
- Vertices occur where the affine subspace meets edges/faces of the box

**Why NOT to use grid search:**
Grid search can miss the true minimum because grid points generally don't coincide with polytope vertices. The action function is piecewise linear, so it varies linearly along edges of the feasible polytope - the minimum is at a vertex, not at arbitrary interior points.

```rust
/// Solve for minimum action trajectory with given edge combination
fn solve_billiard_lp(
    k_q: &Polygon2D,
    k_p: &Polygon2D,
    combo: &EdgeCombination,
) -> Option<(f64, BilliardTrajectory)> {
    let k = combo.q_edges.len();

    match k {
        2 => solve_2bounce(k_q, k_p, combo),
        3 => solve_3bounce(k_q, k_p, combo),
        _ => None,  // Only k=2,3 are valid per bounce bound theorem
    }
}

/// Solve 2-bounce case: enumerate all 16 vertices of [0,1]^4
/// Correctness: By Vertex Optimality Theorem (Section 1.5), minimum of
/// piecewise linear convex function over box is at a vertex.
fn solve_2bounce(
    k_q: &Polygon2D,
    k_p: &Polygon2D,
    combo: &EdgeCombination,
) -> Option<(f64, BilliardTrajectory)> {
    let mut best: Option<(f64, BilliardTrajectory)> = None;

    // Enumerate all 16 vertices of [0,1]^4
    // Each t_i ∈ {0, 1} corresponds to a polygon vertex
    for &t_q0 in &[0.0, 1.0] {
        for &t_q1 in &[0.0, 1.0] {
            for &t_p0 in &[0.0, 1.0] {
                for &t_p1 in &[0.0, 1.0] {
                    if let Some(traj) = build_trajectory(k_q, k_p, combo,
                        &[t_q0, t_q1], &[t_p0, t_p1]) {
                        let action = compute_action(&traj, k_p);
                        if action > MIN_ACTION {
                            if best.is_none() || action < best.as_ref().unwrap().0 {
                                best = Some((action, traj));
                            }
                        }
                    }
                }
            }
        }
    }
    best
}

/// Solve 3-bounce case: enumerate vertices of feasible polytope
/// Correctness: By Vertex Optimality Theorem (Section 1.5), minimum of
/// piecewise linear convex function over polytope is at a vertex.
fn solve_3bounce(
    k_q: &Polygon2D,
    k_p: &Polygon2D,
    combo: &EdgeCombination,
) -> Option<(f64, BilliardTrajectory)> {
    // Build the feasible polytope:
    // - Variables: (t_q0, t_q1, t_q2, t_p0, t_p1, t_p2) ∈ [0,1]^6
    // - Closure: A_q * t_q = b_q (2 equations), A_p * t_p = b_p (2 equations)
    //
    // The q-closure and p-closure are independent, so we can solve separately:
    // 1. Find vertices of {t_q ∈ [0,1]³ : A_q * t_q = b_q}
    // 2. Find vertices of {t_p ∈ [0,1]³ : A_p * t_p = b_p}
    // 3. Cartesian product gives vertices of full feasible set

    let q_vertices = enumerate_affine_box_vertices(k_q, combo, true)?;
    let p_vertices = enumerate_affine_box_vertices(k_p, combo, false)?;

    let mut best: Option<(f64, BilliardTrajectory)> = None;

    for t_q in &q_vertices {
        for t_p in &p_vertices {
            if let Some(traj) = build_trajectory(k_q, k_p, combo, t_q, t_p) {
                let action = compute_action(&traj, k_p);
                if action > MIN_ACTION {
                    if best.is_none() || action < best.as_ref().unwrap().0 {
                        best = Some((action, traj));
                    }
                }
            }
        }
    }
    best
}

/// Enumerate vertices of {t ∈ [0,1]³ : A*t = b} (2D affine subspace ∩ 3D box)
/// Returns None if infeasible (empty intersection)
fn enumerate_affine_box_vertices(
    polygon: &Polygon2D,
    combo: &EdgeCombination,
    is_q_space: bool,
) -> Option<Vec<[f64; 3]>> {
    // The closure constraint Σ Δx_i = 0 where Δx_i depends linearly on t_i
    // gives a 2x3 system A*t = b
    //
    // Strategy: The feasible set is a (possibly empty) convex polygon in [0,1]³.
    // Its vertices occur at intersections of:
    // - The 2D affine plane with edges of the cube (where one t_j ∈ {0, 1})
    // - Or at corners of the cube (where two t_j ∈ {0, 1})
    //
    // Implementation: For each of the 12 edges of [0,1]³, check if the
    // affine plane intersects it. Collect all intersection points.

    let edges = &combo.q_edges; // or p_edges based on is_q_space

    // Build closure matrix: each row is a component of Σ(x_{i+1} - x_i) = 0
    // This is linear in (t_0, t_1, t_2)
    let (a, b) = build_closure_matrix(polygon, edges);

    let mut vertices = Vec::new();

    // Check all 12 edges of the unit cube [0,1]³
    // Each edge fixes 2 coordinates, varies 1
    for fixed1 in 0..3 {
        for fixed2 in (fixed1 + 1)..3 {
            let varying = 3 - fixed1 - fixed2;
            for &val1 in &[0.0, 1.0] {
                for &val2 in &[0.0, 1.0] {
                    // Try to solve for the varying coordinate
                    if let Some(val_v) = solve_for_varying(&a, &b, varying, fixed1, val1, fixed2, val2) {
                        if val_v >= -EDGE_PARAM_TOL && val_v <= 1.0 + EDGE_PARAM_TOL {
                            let mut t = [0.0; 3];
                            t[fixed1] = val1;
                            t[fixed2] = val2;
                            t[varying] = val_v.clamp(0.0, 1.0);
                            vertices.push(t);
                        }
                    }
                }
            }
        }
    }

    // Also check the 8 corners of the cube (in case plane passes through)
    for &t0 in &[0.0, 1.0] {
        for &t1 in &[0.0, 1.0] {
            for &t2 in &[0.0, 1.0] {
                let t = [t0, t1, t2];
                if satisfies_closure(&a, &b, &t, CONSTRAINT_TOL) {
                    vertices.push(t);
                }
            }
        }
    }

    // Remove duplicates (within tolerance)
    vertices = deduplicate_points(vertices, EDGE_PARAM_TOL);

    if vertices.is_empty() {
        None  // Infeasible: no valid trajectory for this edge combination
    } else {
        Some(vertices)
    }
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
| Triangle × Triangle (circumradius 1) | (smoke test) | — | Verify no NaN/Error |
| Simplex_q × Simplex_p (2D) | (smoke test) | — | Verify no NaN/Error |

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

#[test]
fn test_tesseract_capacity() {
    // Tesseract [-1,1]^4 = Square[-1,1]² × Square[-1,1]²
    // Known capacity = 4.0 (HK2017 Example 4.6)
    let square = Polygon2D::square(2.0);  // Side length 2, centered at origin

    let result = billiard_capacity(&square, &square);

    assert!((result.capacity - 4.0).abs() < 1e-6,
        "Tesseract capacity: expected 4.0, got {}", result.capacity);

    // Witness should be a 2-bounce trajectory
    assert!(result.witness.num_bounces == 2,
        "Tesseract minimum should be 2-bounce");
}

#[test]
fn test_smoke_triangle_product() {
    // No ground truth value known, just verify algorithm runs without error
    let triangle = Polygon2D::regular(3, 1.0);  // Equilateral, circumradius 1

    let result = billiard_capacity(&triangle, &triangle);

    assert!(result.capacity.is_finite(), "Capacity should be finite (not NaN/Inf)");
    assert!(result.capacity > 0.0, "Capacity should be positive");
    assert!(result.witness.is_valid(), "Witness should be valid");
}

#[test]
fn test_smoke_simplex_product() {
    // 2D simplex = triangle, just with different construction
    let simplex_q = Polygon2D::simplex();  // Standard 2-simplex
    let simplex_p = Polygon2D::simplex();

    let result = billiard_capacity(&simplex_q, &simplex_p);

    assert!(result.capacity.is_finite(), "Capacity should be finite (not NaN/Inf)");
    assert!(result.capacity > 0.0, "Capacity should be positive");
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

### 5.5 Vertex Optimality Tests

These tests verify the mathematical claim from Section 1.5: the minimum of a piecewise linear convex function over a polytope occurs at a vertex.

```rust
#[test]
fn test_vertex_optimality_2bounce() {
    // For 2-bounce, the minimum must be at one of the 16 corners of [0,1]^4
    // This test verifies that sampling interior points never finds a better minimum
    let k_q = regular_pentagon();
    let k_p = rotate_polygon(&k_q, PI / 2.0);

    // Get the vertex-based minimum
    let result = billiard_capacity(&k_q, &k_p);
    let vertex_min = result.capacity;

    // Sample many interior points and verify none beats the vertex minimum
    let mut rng = rand::thread_rng();
    for _ in 0..1000 {
        // Random interior point in [0,1]^4
        let t_q0 = rng.gen::<f64>();
        let t_q1 = rng.gen::<f64>();
        let t_p0 = rng.gen::<f64>();
        let t_p1 = rng.gen::<f64>();

        // Compute action at this interior point (for some edge combo)
        // ... implementation details ...

        // Assert: interior action >= vertex_min (by convexity)
    }
}

#[test]
fn test_vertex_optimality_3bounce() {
    // For 3-bounce, minimum is at a vertex of the feasible polytope
    // (intersection of closure constraints with [0,1]^6)
    // Test that the vertex enumeration finds the same minimum as exhaustive search

    let k_q = Polygon2D::square(2.0);
    let k_p = Polygon2D::square(2.0);

    // Vertex enumeration result
    let vertex_result = solve_3bounce_vertex_enum(&k_q, &k_p);

    // Dense grid search (as sanity check - should find same or worse)
    let grid_result = solve_3bounce_dense_grid(&k_q, &k_p, 100);  // 100^2 grid

    // The vertex enumeration should find the true minimum
    // Grid search might find the same (if lucky) or slightly worse
    assert!(vertex_result.capacity <= grid_result.capacity + 1e-6,
        "Vertex enum should be optimal: vertex={}, grid={}",
        vertex_result.capacity, grid_result.capacity);
}

#[test]
fn test_piecewise_linear_structure() {
    // Verify that the action function is indeed piecewise linear
    // by checking linearity along edges of the parameter space

    let k_q = regular_pentagon();
    let k_p = rotate_polygon(&k_q, PI / 2.0);

    // Pick an edge combination
    let combo = EdgeCombination { q_edges: vec![0, 1], p_edges: vec![0, 1] };

    // Sample along an edge of the parameter box (varying one t while others fixed)
    let t_q1 = 0.5;
    let t_p0 = 0.0;
    let t_p1 = 1.0;

    let mut actions = Vec::new();
    for i in 0..=10 {
        let t_q0 = i as f64 / 10.0;
        if let Some(traj) = build_trajectory(&k_q, &k_p, &combo,
            &[t_q0, t_q1], &[t_p0, t_p1]) {
            actions.push((t_q0, compute_action(&traj, &k_p)));
        }
    }

    // Check piecewise linearity: action should be linear between "kinks"
    // (where the max in the support function switches which vertex achieves it)
    // At minimum, verify convexity: a[i] <= (a[i-1] + a[i+1]) / 2
    for i in 1..actions.len() - 1 {
        let midpoint = (actions[i - 1].1 + actions[i + 1].1) / 2.0;
        assert!(actions[i].1 <= midpoint + 1e-9,
            "Action should be convex: a[{}]={} > midpoint={}",
            i, actions[i].1, midpoint);
    }
}
```

### 5.6 Input Validation Tests

The billiard algorithm only works for Lagrangian products. These tests verify proper rejection of invalid inputs.

```rust
#[test]
fn test_rejects_non_lagrangian_product() {
    // A polytope with mixed (q,p) facet normals is NOT a Lagrangian product
    let mixed_normals = vec![
        Vector4::new(1.0, 0.0, 0.0, 0.0),   // Pure q-facet
        Vector4::new(0.0, 1.0, 0.0, 0.0),   // Pure q-facet
        Vector4::new(0.0, 0.0, 1.0, 0.0),   // Pure p-facet
        Vector4::new(0.5, 0.0, 0.5, 0.0),   // MIXED - not Lagrangian!
    ];
    let heights = vec![1.0; 4];
    let hrep = PolytopeHRep { normals: mixed_normals, heights };

    let result = extract_lagrangian_factors(&hrep);
    assert!(result.is_none(), "Should reject non-Lagrangian polytope");
}

#[test]
fn test_rejects_degenerate_polygon() {
    // Polygon with collinear vertices (not valid)
    let collinear_vertices = vec![
        Vector2::new(0.0, 0.0),
        Vector2::new(1.0, 0.0),
        Vector2::new(2.0, 0.0),  // Collinear with first two
    ];

    // This should fail validation
    let result = Polygon2D::from_vertices(&collinear_vertices);
    assert!(result.is_err() || result.unwrap().validate().is_err());
}

#[test]
fn test_rejects_polygon_with_origin_outside() {
    // Polygon that doesn't contain 0 in interior (required for valid K)
    let k_q = Polygon2D::square(1.0);
    let k_p = translate_polygon(&Polygon2D::square(1.0), &Vector2::new(10.0, 10.0));
    // k_p is now far from origin - should fail validation

    assert!(k_p.validate().is_err(),
        "Polygon with 0 outside should fail validation");
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

- **Rudolf 2021:** Rudolf, D. "Minkowski billiards and symplectic capacities." *Journal of Modern Dynamics* 17 (2021): 189-216. arXiv:2203.01718.
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

The billiard characterization extends to \(\mathbb{R}^{2n}\) for n > 2 (Rudolf 2021). The bounce bound becomes n+1 (Bezdek-Bezdek Lemma 2.1), making enumeration O(edges^{n+1}).
