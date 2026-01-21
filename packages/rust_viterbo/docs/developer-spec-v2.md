# Developer Specification for EHZ Capacity Algorithms

> **Audience:** Claude Code agents implementing the algorithms
> **Prerequisite:** Read thesis chapter ([algorithms.tex](../../latex_viterbo/chapters/algorithms.tex)) for mathematical background
> **Status:** This document consolidates all algorithm specifications. Implementation archived at tag `v0.1.0-archive`.

---

## Table of Contents

0. [Problem Statement](#0-problem-statement)
   - What We Compute
   - The EHZ Capacity
   - Capacity Axioms
   - Document Structure

1. [Data about the Polytope K](#1-data-about-the-polytope-k)
   - 1.1 H-Representation
   - 1.2 V-Representation
   - 1.3 Reeb Vectors
   - 1.4 Symplectic Form
   - 1.5 Complex Structure J
   - 1.6 Facets and 2-Faces
   - 1.7 Lagrangian 2-Faces
   - 1.8 Adjacency Graph
   - 1.9 2D Polygons
   - 1.10 Quaternion Structure
   - 1.11 Trivialization
   - 1.12 Transition Matrices
   - 1.13 Rotation Number
   - 1.14 Support Function and Polar Body
   - 1.15 Trivialized 2-Face Polygons
   - 1.16 Edge and Vertex Incidence
   - 1.17 Constants and Tolerances

2. [Data about Reeb Trajectories and Orbits](#2-data-about-reeb-trajectories-and-orbits)
   - 2.1 Closed Curves and Action
   - 2.2 Curves on the Boundary
   - 2.3 Reeb Trajectories (Differential Inclusion)
   - 2.4 Piecewise Linear Reeb Trajectories
   - 2.5 Action of Piecewise Linear Trajectories
   - 2.6 Closed Reeb Orbits
   - 2.7 Simple Reeb Orbits
   - 2.8 Facet Sequences and Combinatorial Classes
   - 2.9 Tubes (Partial Trajectories)
   - 2.10 Tube Extension
   - 2.11 Tube Closure
   - 2.12 Reconstruction: 2D to 4D
   - 2.13 Validity Checks

3. [Algorithms](#3-algorithms)
   - 3.1 Algorithm Applicability Summary
   - 3.2 Billiard Algorithm
   - 3.3 HK2017 Quadratic Programming
   - 3.4 Tube Algorithm

4. [Test Cases and Verification Properties](#4-test-cases-and-verification-properties)
   - 4.1 Ground Truth Values
   - 4.2 Capacity Axioms
   - 4.3 Orbit Validity Tests
   - 4.4 Algorithm Agreement
   - 4.5 Geometric Foundation Tests
   - 4.6 Tube Algorithm Tests
   - 4.7 Polytope Data Consistency
   - 4.8 Test Fixtures

---

## 0. Problem Statement

### What We Compute

**Input:** A polytope \(K \subset \mathbb{R}^4\) with \(0 \in \mathrm{int}(K)\).

**Output:** The Ekeland-Hofer-Zehnder capacity \(c_{\text{EHZ}}(K)\) and a minimum-action closed Reeb orbit achieving it.

### The EHZ Capacity

The **EHZ capacity** \(c_{\text{EHZ}}(K)\) is the minimum symplectic action over all closed Reeb orbits on \(\partial K\):
\[
c_{\text{EHZ}}(K) = \min \{ A(\gamma) : \gamma \text{ is a closed Reeb orbit on } \partial K \}
\]

**Why it matters:**
- \(c_{\text{EHZ}}\) is a symplectic invariant: preserved under symplectomorphisms
- It measures the "symplectic size" of \(K\)
- Viterbo's conjecture (now known to be false) predicted \(c_{\text{EHZ}}(K)^2 \leq 2 \cdot \text{Vol}(K)\)
- The HK-O 2024 counterexample (pentagon × rotated pentagon) has \(c^2 / (2 \cdot \text{Vol}) \approx 1.047 > 1\)

### Capacity Axioms (What Tests Should Verify)

1. **Scaling:** \(c(\lambda K) = \lambda^2 \cdot c(K)\) for \(\lambda > 0\)
2. **Monotonicity:** \(K \subseteq L \Rightarrow c(K) \leq c(L)\)
3. **Symplectic invariance:** \(c(AK) = c(K)\) for \(A \in \text{Sp}(4)\)
4. **Conformality:** \(c(B^4) = c(Z^4) = \pi\) (ball and cylinder)

### Document Structure

- **Part 1:** Data about the polytope \(K\) — all derived quantities needed by algorithms
- **Part 2:** Data about Reeb trajectories and orbits — representations and validity conditions
- **Part 3:** Algorithms — Billiard, HK2017, Tube
- **Part 4:** Test cases — properties that detect bugs when code diverges from math

---

## 1. Data about the Polytope K

Throughout this document, \(K \subset \mathbb{R}^4\) is a fixed polytope with \(0 \in \mathrm{int}(K)\).

A **polytope** is equivalently:
- The convex hull of finitely many points, with nonempty interior
- The bounded intersection of finitely many half-spaces, with nonempty interior

We work in standard symplectic \(\mathbb{R}^4\) with coordinates \((q_1, q_2, p_1, p_2)\).

---

### 1.1 H-Representation (Input)

The **H-representation** defines \(K\) as an intersection of half-spaces:
\[
K = \bigcap_{i=0}^{F-1} \{ x \in \mathbb{R}^4 : \langle n_i, x \rangle \leq h_i \}
\]

This is a natural input format because:
- Compact: \(O(F)\) data for \(F\) facets
- The algorithms work directly with facet normals
- Converting V-rep → H-rep requires vertex enumeration (expensive)

```rust
struct PolytopeHRep {
    normals: Vec<[f64; 4]>,
    heights: Vec<f64>,
}
```

**Derived:**
```rust
let num_facets: usize = normals.len();
```

**Assertions:**
```rust
assert!(normals.len() == heights.len());           // arrays match
assert!(normals.iter().all(|n| is_unit(n)));       // normalized
assert!(heights.iter().all(|&h| h > 0.0));         // 0 in interior
assert!(normals.iter().all(|n| !has_nan(n)));      // no NaNs
assert!(heights.iter().all(|&h| !h.is_nan()));
```

**If assertions fail:**
- `heights[i] <= 0` → origin not in interior, violates \(0 \in \mathrm{int}(K)\)
- `||n_i|| != 1` → not normalized, caller must normalize before passing
- Array length mismatch → malformed input

**Conventions:**
- **Normalized:** \(\|n_i\| = 1\) (unit outward normals)
- **Non-redundant:** Every half-space defines a facet (checked later, requires more computation)

---

### 1.2 V-Representation (Vertices)

The **V-representation** defines \(K\) as a convex hull:
\[
K = \mathrm{conv}(\{v_0, v_1, \ldots, v_{V-1}\})
\]

Vertices can be computed from H-rep via vertex enumeration (e.g., double description method).

```rust
let vertices: Vec<[f64; 4]> = vertex_enumeration(&hrep);
let num_vertices: usize = vertices.len();
```

**Assertions:**
```rust
// Each vertex lies on the boundary (at least one tight constraint)
assert!(vertices.iter().all(|v|
    hrep.normals.iter().zip(&hrep.heights)
        .any(|(n, &h)| (dot(n, v) - h).abs() < EPS)
));

// Each vertex satisfies all constraints
assert!(vertices.iter().all(|v|
    hrep.normals.iter().zip(&hrep.heights)
        .all(|(n, &h)| dot(n, v) <= h + EPS)
));

// Origin is in interior of convex hull
assert!(is_in_interior_of_convex_hull(&[0.0; 4], &vertices));
```

**Non-redundancy check for H-rep** (now possible with vertices):
```rust
// Every facet has at least 4 vertices (since dim = 4, facets are 3-dimensional)
for i in 0..num_facets {
    let verts_on_facet: Vec<_> = vertices.iter()
        .filter(|v| (dot(&hrep.normals[i], v) - hrep.heights[i]).abs() < EPS)
        .collect();
    assert!(verts_on_facet.len() >= 4, "facet {} is redundant or degenerate", i);
}
```

---

### 1.3 Facets (3-faces)

A **facet** \(F_i\) is the intersection of \(K\) with the \(i\)-th bounding hyperplane:
\[
F_i = K \cap \{ x : \langle n_i, x \rangle = h_i \}
\]

Facets are 3-dimensional convex polytopes. We index them by \(i \in \{0, \ldots, F-1\}\).

```rust
struct Facet {
    index: usize,              // i
    normal: [f64; 4],          // n_i (outward unit normal)
    height: f64,               // h_i
    vertices: Vec<usize>,      // indices into the global vertex list
}

let facets: Vec<Facet> = (0..num_facets).map(|i| {
    let verts: Vec<usize> = (0..num_vertices)
        .filter(|&j| (dot(&normals[i], &vertices[j]) - heights[i]).abs() < EPS)
        .collect();
    Facet { index: i, normal: normals[i], height: heights[i], vertices: verts }
}).collect();
```

**Assertions:**
```rust
assert!(facets.iter().all(|f| f.vertices.len() >= 4));  // 3D polytope needs >= 4 vertices
```

---

### 1.4 Reeb Vectors

The **Reeb vector** on facet \(F_i\) is the direction of the Reeb flow:
\[
R_i = \frac{2}{h_i} J n_i
\]

where \(J\) is the standard complex structure:
\[
J(q_1, q_2, p_1, p_2) = (-p_1, -p_2, q_1, q_2)
\]

```rust
fn complex_structure(v: [f64; 4]) -> [f64; 4] {
    [-v[2], -v[3], v[0], v[1]]
}

let reeb_vectors: Vec<[f64; 4]> = (0..num_facets)
    .map(|i| {
        let jn = complex_structure(normals[i]);
        scale(2.0 / heights[i], jn)
    })
    .collect();
```

**Assertions:**
```rust
// Reeb vectors are perpendicular to their facet normal
assert!(reeb_vectors.iter().zip(&normals)
    .all(|(r, n)| dot(r, n).abs() < EPS));

// Reeb vectors have magnitude 2/h_i
assert!(reeb_vectors.iter().zip(&heights)
    .all(|(r, &h)| (norm(r) - 2.0/h).abs() < EPS));
```

---

### 1.5 Symplectic Form

The **symplectic form** \(\omega\) on \(\mathbb{R}^4\):
\[
\omega(x, y) = \langle Jx, y \rangle = q_1 p_1' + q_2 p_2' - p_1 q_1' - p_2 q_2'
\]

```rust
fn symplectic_form(x: [f64; 4], y: [f64; 4]) -> f64 {
    let jx = complex_structure(x);
    dot(&jx, &y)
}
```

**Properties:**
- Antisymmetric: \(\omega(x, y) = -\omega(y, x)\)
- Non-degenerate: \(\omega(x, y) = 0\) for all \(y\) implies \(x = 0\)

**Standard basis pairings:**
```rust
assert_eq!(symplectic_form([1,0,0,0], [0,0,1,0]),  1.0);  // omega(e_1, e_3) = 1
assert_eq!(symplectic_form([0,1,0,0], [0,0,0,1]),  1.0);  // omega(e_2, e_4) = 1
assert_eq!(symplectic_form([1,0,0,0], [0,1,0,0]),  0.0);  // omega(e_1, e_2) = 0 (Lagrangian)
assert_eq!(symplectic_form([0,0,1,0], [0,0,0,1]),  0.0);  // omega(e_3, e_4) = 0 (Lagrangian)
```

---

### 1.6 Two-Faces and Adjacency

A **2-face** \(F_{ij}\) is the intersection of two facets:
\[
F_{ij} = F_i \cap F_j = K \cap \{ x : \langle n_i, x \rangle = h_i \} \cap \{ x : \langle n_j, x \rangle = h_j \}
\]

Two facets are **adjacent** iff their 2-face is nonempty (and 2-dimensional).

```rust
struct TwoFace {
    i: usize,                  // first facet index (i < j by convention)
    j: usize,                  // second facet index
    vertices: Vec<usize>,      // indices of vertices on this 2-face
    omega_ij: f64,             // symplectic form of normals: omega(n_i, n_j)
}
```

**Note:** For the Tube algorithm, 2-faces are enriched with additional data (transition matrices, trivialized polygons, rotation numbers). These fields are defined in sections 1.11-1.15 and collected in `TwoFaceEnriched`.

```rust
let two_faces: Vec<TwoFace> = {
    let mut faces = Vec::new();
    for i in 0..num_facets {
        for j in (i+1)..num_facets {
            let verts: Vec<usize> = (0..num_vertices)
                .filter(|&k|
                    (dot(&normals[i], &vertices[k]) - heights[i]).abs() < EPS &&
                    (dot(&normals[j], &vertices[k]) - heights[j]).abs() < EPS
                )
                .collect();
            if verts.len() >= 3 {  // 2D face needs >= 3 vertices
                let omega_ij = symplectic_form(normals[i], normals[j]);
                faces.push(TwoFace { i, j, vertices: verts, omega_ij });
            }
        }
    }
    faces
};
```

**Adjacency matrix:**
```rust
let adjacent: Vec<Vec<bool>> = /* F x F matrix where adjacent[i][j] = true iff F_ij exists */;
```

---

### 1.7 Lagrangian vs Non-Lagrangian 2-Faces

A 2-face \(F_{ij}\) is **Lagrangian** iff \(\omega(n_i, n_j) = 0\).

```rust
impl TwoFace {
    fn is_lagrangian(&self) -> bool {
        self.omega_ij.abs() < EPS_LAGRANGIAN
    }
}

let lagrangian_two_faces: Vec<&TwoFace> = two_faces.iter()
    .filter(|f| f.is_lagrangian())
    .collect();

let non_lagrangian_two_faces: Vec<&TwoFace> = two_faces.iter()
    .filter(|f| !f.is_lagrangian())
    .collect();
```

**Significance:**
- The Tube algorithm requires non-Lagrangian 2-faces (Reeb flow crosses between facets)
- A **Lagrangian product** \(K_1 \times K_2 \subset \mathbb{R}^2_q \times \mathbb{R}^2_p\) has ALL 2-faces Lagrangian
- If some but not all 2-faces are Lagrangian, special handling may be needed

---

### 1.8 Flow Direction on Non-Lagrangian 2-Faces

For a non-Lagrangian 2-face \(F_{ij}\), the Reeb flow crosses from one facet to the other. The direction depends on the sign of \(\omega(n_i, n_j)\):

```rust
enum FlowDirection {
    ItoJ,  // flow crosses from F_i to F_j
    JtoI,  // flow crosses from F_j to F_i
}

impl TwoFace {
    fn flow_direction(&self) -> Option<FlowDirection> {
        if self.is_lagrangian() {
            None  // no crossing on Lagrangian faces
        } else if self.omega_ij > 0.0 {
            Some(FlowDirection::ItoJ)
        } else {
            Some(FlowDirection::JtoI)
        }
    }
}
```

---

### 1.9 Lagrangian Product Structure (Special Case)

\(K\) is a **Lagrangian product** iff \(K = K_1 \times K_2\) where:
- \(K_1 \subset \mathbb{R}^2_q\) (configuration space, coordinates \(q_1, q_2\))
- \(K_2 \subset \mathbb{R}^2_p\) (momentum space, coordinates \(p_1, p_2\))

**Detection:** Check if every facet normal has either:
- Only \(q\)-coordinates nonzero: \(n = (n_{q_1}, n_{q_2}, 0, 0)\)
- Only \(p\)-coordinates nonzero: \(n = (0, 0, n_{p_1}, n_{p_2})\)

```rust
fn is_lagrangian_product(hrep: &PolytopeHRep) -> bool {
    hrep.normals.iter().all(|n| {
        let q_part = n[0].abs() + n[1].abs();
        let p_part = n[2].abs() + n[3].abs();
        (q_part < EPS) || (p_part < EPS)  // one part must be zero
    })
}
```

If true, extract the 2D factors:

```rust
struct LagrangianFactors {
    Kq: Polygon2D,  // factor in q-space
    Kp: Polygon2D,  // factor in p-space
}

struct Polygon2D {
    normals: Vec<[f64; 2]>,    // unit outward normals, CCW order
    heights: Vec<f64>,
    vertices: Vec<[f64; 2]>,   // CCW order, vertex[i] is intersection of edges i-1 and i
}
```

---

### 1.10 Quaternion Structure

For trivializing 2-faces, we use the quaternion matrices on \(\mathbb{R}^4\):

\[
I = \text{identity}, \quad
J = \begin{pmatrix} 0 & 0 & -1 & 0 \\ 0 & 0 & 0 & -1 \\ 1 & 0 & 0 & 0 \\ 0 & 1 & 0 & 0 \end{pmatrix}, \quad
K = \begin{pmatrix} 0 & -1 & 0 & 0 \\ 1 & 0 & 0 & 0 \\ 0 & 0 & 0 & 1 \\ 0 & 0 & -1 & 0 \end{pmatrix}
\]

```rust
fn J(v: [f64; 4]) -> [f64; 4] {
    [-v[2], -v[3], v[0], v[1]]
}

fn K(v: [f64; 4]) -> [f64; 4] {
    [-v[1], v[0], v[3], -v[2]]
}
```

**Relations:** \(I^2 = J^2 = K^2 = IJK = -I\)

```rust
assert_eq!(J(J(v)), scale(-1.0, v));  // J² = -I
assert_eq!(K(K(v)), scale(-1.0, v));  // K² = -I
assert_eq!(J(K(v)), scale(-1.0, K(J(v))));  // JK = -KJ
```

---

### 1.11 Trivialization of 2-Face Tangent Spaces

Each non-Lagrangian 2-face \(F_{ij}\) has a 2-dimensional tangent space. We trivialize it using the quaternion structure.

**Setup:** For a 2-face \(F_{ij} = F_i \cap F_j\), the tangent space is:
\[
T_p F_{ij} = \{ V \in \mathbb{R}^4 : \langle V, n_i \rangle = 0 \text{ and } \langle V, n_j \rangle = 0 \}
\]
This is 2-dimensional (intersection of two hyperplanes in 4D).

**Definition:** The trivialization \(\tau_n: \mathbb{R}^4 \to \mathbb{R}^2\) with respect to unit normal \(n\):
\[
\tau_n(V) = (\langle V, Jn \rangle, \langle V, Kn \rangle)
\]

```rust
fn trivialize(n: [f64; 4], v: [f64; 4]) -> [f64; 2] {
    [dot(&v, &J(n)), dot(&v, &K(n))]
}
```

**Note:** This function can be applied to any \(V \in \mathbb{R}^4\), but its geometric meaning requires \(V\) tangent to the facet (i.e., \(\langle V, n \rangle = 0\)).

**Inverse:** Given 2D coordinates \((a, b)\) and the trivialization basis:
\[
\tau_n^{-1}(a, b) = a \cdot Jn + b \cdot Kn
\]

```rust
fn untrivialize(n: [f64; 4], coords: [f64; 2]) -> [f64; 4] {
    add(scale(coords[0], J(n)), scale(coords[1], K(n)))
}
```

**Assertions:**
```rust
// Jn and Kn are orthonormal (basis for the tangent hyperplane restricted to symplectic complement)
assert!((dot(&J(n), &K(n))).abs() < EPS);  // orthogonal
assert!((norm(&J(n)) - 1.0).abs() < EPS);  // unit length
assert!((norm(&K(n)) - 1.0).abs() < EPS);  // unit length

// Jn and Kn are tangent to the facet (perpendicular to n)
assert!(dot(&J(n), &n).abs() < EPS);
assert!(dot(&K(n), &n).abs() < EPS);

// Round-trip: untrivialize ∘ trivialize = identity on tangent vectors
// (only holds for vectors perpendicular to n)
let v_tangent = /* any vector with dot(v, n) == 0 */;
let v_recovered = untrivialize(n, trivialize(n, v_tangent));
assert!(norm(&sub(v_recovered, v_tangent)) < EPS);
```

**Key property (symplectic form preservation):**

For vectors \(V_1, V_2\) **tangent to the facet** (i.e., \(\langle V_i, n \rangle = 0\)):
\[
\omega(V_1, V_2) = \omega_{\text{std}}(\tau_n(V_1), \tau_n(V_2))
\]
where \(\omega_{\text{std}}(x, y) = x_1 y_2 - x_2 y_1\) is the standard 2D symplectic form.

**Mathematical condition (not encoded in Rust type):** The symplectic form preservation only holds when both input vectors are perpendicular to \(n\).

```rust
fn symplectic_form_2d(x: [f64; 2], y: [f64; 2]) -> f64 {
    x[0] * y[1] - x[1] * y[0]
}

// Verification (requires v1, v2 tangent to facet):
fn verify_symplectic_preservation(n: [f64; 4], v1: [f64; 4], v2: [f64; 4]) {
    // Precondition: v1, v2 are tangent to the facet
    assert!(dot(&v1, &n).abs() < EPS, "v1 not tangent to facet");
    assert!(dot(&v2, &n).abs() < EPS, "v2 not tangent to facet");

    let omega_4d = symplectic_form(v1, v2);
    let omega_2d = symplectic_form_2d(trivialize(n, v1), trivialize(n, v2));
    assert!((omega_4d - omega_2d).abs() < EPS);
}
```

---

### 1.12 Transition Matrices on 2-Faces

For a non-Lagrangian 2-face \(F_{ij}\), the **transition matrix** \(\psi_F \in \mathrm{Sp}(2)\) relates the trivializations from the two adjacent facet normals:
\[
\psi_F = \tau_{n_j} \circ \tau_{n_i}^{-1}
\]

This is a 2×2 symplectic matrix encoding how coordinates transform when crossing the 2-face.

```rust
struct TwoFaceEnriched {
    // ... previous fields ...
    transition_matrix: [[f64; 2]; 2],  // ψ_F ∈ Sp(2)
}

fn compute_transition_matrix(n_i: [f64; 4], n_j: [f64; 4]) -> [[f64; 2]; 2] {
    // ψ_F maps τ_{n_i} coordinates to τ_{n_j} coordinates
    // Column k of ψ is τ_{n_j}(τ_{n_i}^{-1}(e_k))
    let e1 = [1.0, 0.0];
    let e2 = [0.0, 1.0];

    let v1 = untrivialize(n_i, e1);  // Jn_i
    let v2 = untrivialize(n_i, e2);  // Kn_i

    let col1 = trivialize(n_j, v1);
    let col2 = trivialize(n_j, v2);

    [[col1[0], col2[0]], [col1[1], col2[1]]]
}
```

**Assertions:**
```rust
// ψ is always symplectic: det(ψ) = 1
assert!((psi[0][0] * psi[1][1] - psi[0][1] * psi[1][0] - 1.0).abs() < EPS);
```

**Classification by trace (mathematical condition not encoded in Rust type):**
- \(|\mathrm{tr}(\psi)| > 2\): Hyperbolic (cannot occur for polytope 2-faces)
- \(|\mathrm{tr}(\psi)| = 2\): Parabolic = Lagrangian 2-face (ω(n_i, n_j) = 0)
- \(|\mathrm{tr}(\psi)| < 2\): Elliptic = non-Lagrangian 2-face

```rust
// For non-Lagrangian 2-faces only: ψ is positive elliptic (|tr| < 2)
// This condition is EQUIVALENT to ω(n_i, n_j) ≠ 0
fn assert_non_lagrangian(psi: [[f64; 2]; 2], n_i: [f64; 4], n_j: [f64; 4]) {
    let trace = psi[0][0] + psi[1][1];
    let omega = symplectic_form(n_i, n_j);

    // Both conditions should agree
    let is_lagrangian_by_trace = (trace.abs() - 2.0).abs() < EPS;
    let is_lagrangian_by_omega = omega.abs() < EPS_LAGRANGIAN;
    assert_eq!(is_lagrangian_by_trace, is_lagrangian_by_omega,
        "Lagrangian detection methods disagree");

    // For Tube algorithm, we require non-Lagrangian
    assert!(trace.abs() < 2.0 - EPS, "2-face is Lagrangian, Tube algorithm inapplicable");
}
```

---

### 1.13 Rotation Number of 2-Faces

For a non-Lagrangian 2-face \(F_{ij}\), the **rotation number** \(\rho(F) \in (0, 0.5)\) measures how much the Reeb flow "rotates" when crossing:
\[
\rho(F) = \frac{1}{2\pi} \arccos\left(\frac{1}{2} \mathrm{tr}(\psi_F)\right)
\]

```rust
impl TwoFaceEnriched {
    fn rotation_number(&self) -> f64 {
        let trace = self.transition_matrix[0][0] + self.transition_matrix[1][1];
        (0.5 * trace).acos() / (2.0 * PI)
    }
}
```

**Classification by trace:**
- \(|\mathrm{tr}| > 2\): Hyperbolic (impossible for non-Lagrangian 2-faces of polytopes)
- \(|\mathrm{tr}| = 2\): Parabolic (boundary case, Lagrangian)
- \(|\mathrm{tr}| < 2\): Elliptic (rotation), with \(\rho \in (0, 0.5)\)

**Significance for Tube algorithm:** Total rotation of a closed orbit must equal an integer. The algorithm prunes paths where accumulated rotation exceeds 2 turns (per CH2021 Prop 1.10).

---

### 1.14 Support Function and Polar Body

The **support function** of \(K\):
\[
h_K(d) = \max_{x \in K} \langle d, x \rangle
\]

For H-rep polytope, this is computable via the vertices:
```rust
fn support_function(vertices: &[[f64; 4]], direction: [f64; 4]) -> f64 {
    vertices.iter()
        .map(|v| dot(&direction, v))
        .fold(f64::NEG_INFINITY, f64::max)
}
```

The **polar body** (dual) of \(K\):
\[
K^\circ = \{ y \in \mathbb{R}^4 : \langle x, y \rangle \leq 1 \text{ for all } x \in K \}
\]

For a 2D polygon in H-rep \(\{x : \langle n_i, x \rangle \leq h_i\}\), the polar has vertices at \(n_i / h_i\):

```rust
fn polar_vertices_2d(normals: &[[f64; 2]], heights: &[f64]) -> Vec<[f64; 2]> {
    normals.iter().zip(heights)
        .map(|(n, &h)| [n[0] / h, n[1] / h])
        .collect()
}
```

**Significance for Billiard algorithm:** The "T-length" of a billiard trajectory is measured using \(K_2^\circ\) as the unit ball, i.e., via \(h_{K_2}(\cdot)\).

---

### 1.15 Trivialized 2-Face Polygons

For the Tube algorithm, we need each 2-face as a 2D polygon in trivialized coordinates.

```rust
struct TwoFaceEnriched {
    // ... previous fields ...
    polygon_2d: Vec<[f64; 2]>,     // vertices in τ_{n_i} coordinates
    vertices_4d: Vec<[f64; 4]>,    // original 4D vertices
    centroid_4d: [f64; 4],         // centroid for reconstruction
}

fn trivialize_two_face(
    two_face: &TwoFace,
    vertices: &[[f64; 4]],
    entry_normal: [f64; 4],
) -> TwoFaceEnriched {
    let verts_4d: Vec<[f64; 4]> = two_face.vertices.iter()
        .map(|&i| vertices[i])
        .collect();

    let centroid = average(&verts_4d);

    // Trivialize relative to centroid
    let polygon_2d: Vec<[f64; 2]> = verts_4d.iter()
        .map(|v| trivialize(entry_normal, sub(*v, centroid)))
        .collect();

    // Sort by angle for CCW ordering
    let polygon_2d = sort_ccw(polygon_2d);

    TwoFaceEnriched {
        // ... copy fields from two_face ...
        polygon_2d,
        vertices_4d: verts_4d,
        centroid_4d: centroid,
        // ...
    }
}
```

**Consolidated TwoFaceEnriched (all fields from sections 1.6, 1.12-1.15):**

```rust
struct TwoFaceEnriched {
    // From 1.6: Basic identification
    i: usize,                          // first facet index (i < j)
    j: usize,                          // second facet index
    vertices: Vec<usize>,              // indices into global vertex list
    omega_ij: f64,                     // ω(n_i, n_j)

    // From 1.7: Lagrangian classification
    is_lagrangian: bool,               // |omega_ij| < EPS_LAGRANGIAN

    // From 1.8: Flow direction (for non-Lagrangian)
    flow_direction: Option<FlowDirection>,  // ItoJ or JtoI

    // From 1.12: Transition matrix (for non-Lagrangian)
    transition_matrix: [[f64; 2]; 2],  // ψ_F ∈ Sp(2)

    // From 1.13: Rotation number (for non-Lagrangian)
    rotation: f64,                     // ρ(F) ∈ (0, 0.5)

    // From 1.15: Trivialized polygon
    polygon_2d: Vec<[f64; 2]>,         // vertices in τ_{n_i} coordinates, CCW
    vertices_4d: Vec<[f64; 4]>,        // original 4D vertex positions
    centroid_4d: [f64; 4],             // centroid for reconstruction
}
```

---

### 1.16 Edge and Vertex Incidence

For computing face lattice and adjacency queries:

```rust
/// Which facets contain vertex v?
fn facets_containing_vertex(v: usize, facets: &[Facet]) -> Vec<usize> {
    facets.iter()
        .filter(|f| f.vertices.contains(&v))
        .map(|f| f.index)
        .collect()
}

/// A vertex lies on exactly dim(K) = 4 facets for a simple polytope
/// (more for non-simple polytopes)
assert!(facets.iter().all(|f|
    f.vertices.iter().all(|&v|
        facets_containing_vertex(v, &facets).len() >= 4
    )
));
```

**1-faces (edges):** An edge is the intersection of 3 facets (in 4D).

```rust
struct Edge {
    v1: usize,
    v2: usize,
    facets: Vec<usize>,  // which facets contain this edge (at least 3)
}
```

---

### 1.17 Constants and Tolerances

```rust
const EPS: f64 = 1e-10;              // general numerical tolerance
const EPS_LAGRANGIAN: f64 = 1e-9;    // threshold for Lagrangian detection
const EPS_UNIT: f64 = 1e-9;          // tolerance for ||n|| = 1 check
const EPS_FEASIBILITY: f64 = 1e-10;  // constraint satisfaction
const EPS_DEDUP: f64 = 1e-8;         // vertex deduplication
const EPS_ROTATION: f64 = 0.01;      // rotation pruning margin (turns)
```

**Tolerance philosophy:**
- Use relative tolerance where possible: `|a - b| < EPS * max(|a|, |b|, 1.0)`
- Tight tolerances for input validation (catch errors early)
- Looser tolerances for derived quantities (numerical error accumulates)
- Document when a tolerance is "engineering choice" vs mathematically motivated

---

## 2. Data about Reeb Trajectories and Orbits

This section defines computational representations for curves on the polytope boundary, with increasing specialization from general closed curves to Reeb orbits to simple Reeb orbits.

---

### 2.1 Closed Curves and Action (General)

A **closed curve** \(\gamma: [0,T] \to \mathbb{R}^4\) with \(\gamma(0) = \gamma(T)\) has a well-defined **action**:
\[
A(\gamma) = \frac{1}{2} \int_0^T \langle J \gamma(t), \dot\gamma(t) \rangle \, dt = \oint_\gamma \lambda
\]
where \(\lambda = \frac{1}{2}(p \, dq - q \, dp)\) is the Liouville 1-form.

**Piecewise linear closed curves** can be represented by their vertices:

```rust
struct ClosedPolygonalCurve {
    vertices: Vec<[f64; 4]>,  // vertices[0], ..., vertices[n-1]
}
```

**Mathematical conditions (not encoded in type):**
- Closure: `vertices[0] == vertices[n-1]` (or implicitly closed: edge from `vertices[n-1]` back to `vertices[0]`)
- No NaNs, no infinities

**Action formula for piecewise linear curves:**

For a closed polygonal curve with vertices \(v_0, v_1, \ldots, v_{n-1}, v_n = v_0\):
\[
A = \frac{1}{2} \sum_{k=0}^{n-1} \langle J v_k, v_{k+1} - v_k \rangle = \frac{1}{2} \sum_{k=0}^{n-1} \omega(v_k, v_{k+1})
\]

```rust
fn action_of_closed_polygon(vertices: &[[f64; 4]]) -> f64 {
    let n = vertices.len();
    let mut sum = 0.0;
    for k in 0..n {
        let v_k = vertices[k];
        let v_next = vertices[(k + 1) % n];
        sum += symplectic_form(v_k, v_next);
    }
    0.5 * sum
}
```

**Assertions:**
```rust
// Action is independent of starting vertex (cyclic invariance)
assert!((action_of_closed_polygon(&rotate_left(vertices, 1)) - action_of_closed_polygon(vertices)).abs() < EPS);

// Action reverses sign under orientation reversal
let reversed: Vec<_> = vertices.iter().rev().cloned().collect();
assert!((action_of_closed_polygon(&reversed) + action_of_closed_polygon(vertices)).abs() < EPS);
```

---

### 2.2 Curves on the Boundary

A curve \(\gamma: [0,T] \to \partial K\) lies on the boundary if every point satisfies at least one facet constraint with equality.

**Condition for point on boundary:**
\[
p \in \partial K \iff \exists i : \langle n_i, p \rangle = h_i \text{ and } \forall j : \langle n_j, p \rangle \leq h_j
\]

```rust
fn is_on_boundary(p: [f64; 4], hrep: &PolytopeHRep) -> bool {
    let on_some_facet = hrep.normals.iter().zip(&hrep.heights)
        .any(|(n, &h)| (dot(n, &p) - h).abs() < EPS);
    let inside_all = hrep.normals.iter().zip(&hrep.heights)
        .all(|(n, &h)| dot(n, &p) <= h + EPS);
    on_some_facet && inside_all
}

fn active_facets(p: [f64; 4], hrep: &PolytopeHRep) -> Vec<usize> {
    hrep.normals.iter().zip(&hrep.heights).enumerate()
        .filter(|(_, (n, &h))| (dot(n, &p) - h).abs() < EPS)
        .map(|(i, _)| i)
        .collect()
}
```

**Assertions:**
```rust
// Boundary points are inside K
assert!(is_inside_or_on_boundary(p, hrep));

// At least one facet is active
assert!(!active_facets(p, hrep).is_empty());
```

---

### 2.3 Reeb Trajectories (Differential Inclusion)

A **Reeb trajectory** is a curve \(\gamma: [0,T] \to \partial K\) satisfying the Reeb flow differential inclusion:
\[
\dot\gamma(t) \in \mathrm{cone}\left\{ R_i : \gamma(t) \in F_i \right\}
\]
where \(R_i = \frac{2}{h_i} J n_i\) is the Reeb vector on facet \(F_i\).

**Reeb vector properties:**
```rust
// Reeb vector is tangent to its facet (perpendicular to normal)
assert!(dot(&reeb_vectors[i], &normals[i]).abs() < EPS);

// Reeb vector magnitude = 2/h_i
assert!((norm(&reeb_vectors[i]) - 2.0 / heights[i]).abs() < EPS);
```

**Cone membership:** At a point on multiple facets, the velocity is a non-negative combination:
\[
\dot\gamma(t) = \sum_{i \in \text{active}(\gamma(t))} \lambda_i R_i, \quad \lambda_i \geq 0
\]

```rust
fn is_valid_reeb_velocity(
    velocity: [f64; 4],
    active_facets: &[usize],
    reeb_vectors: &[[f64; 4]],
) -> bool {
    // Solve: velocity = Σ λ_i R_i with λ_i ≥ 0
    // This is a linear feasibility problem
    solve_cone_membership(velocity, active_facets, reeb_vectors)
}
```

---

### 2.4 Piecewise Linear Reeb Trajectories

A piecewise linear Reeb trajectory has:
- **Breakpoints**: positions where velocity changes
- **Segments**: straight-line paths between breakpoints, each with constant Reeb velocity
- **Segment times**: duration spent on each segment

```rust
struct PiecewiseLinearReebTrajectory {
    breakpoints: Vec<[f64; 4]>,   // p_0, p_1, ..., p_m
    segment_facets: Vec<usize>,   // which facet's Reeb vector for each segment
    segment_times: Vec<f64>,      // duration of each segment
}
```

**Mathematical conditions (not encoded in type):**
1. Each breakpoint lies on \(\partial K\)
2. Each segment lies on its claimed facet: both endpoints satisfy \(\langle n_i, p \rangle = h_i\)
3. Velocity = Reeb vector: \((p_{k+1} - p_k) / \tau_k = R_{i_k}\)
4. Times positive: \(\tau_k > 0\)

**Segment time formula (derived from velocity constraint):**

Given breakpoints \(p_k, p_{k+1}\) on facet \(i\):
\[
\tau_k = \frac{\|p_{k+1} - p_k\|}{\|R_i\|} = \frac{h_i \cdot \|p_{k+1} - p_k\|}{2}
\]

Equivalently, since \(p_{k+1} - p_k = \tau_k \cdot R_i\):
\[
\tau_k = \frac{h_i}{2} \cdot \|p_{k+1} - p_k\|
\]

```rust
fn compute_segment_time(
    p_start: [f64; 4],
    p_end: [f64; 4],
    facet_idx: usize,
    heights: &[f64],
) -> f64 {
    let displacement = norm(&sub(p_end, p_start));
    heights[facet_idx] * displacement / 2.0
}
```

**Assertions:**
```rust
// Velocity matches Reeb vector
let velocity = scale(1.0 / segment_times[k], sub(breakpoints[k+1], breakpoints[k]));
let expected_velocity = reeb_vectors[segment_facets[k]];
assert!(norm(&sub(velocity, expected_velocity)) < EPS);

// Both endpoints on claimed facet
assert!((dot(&normals[i], &breakpoints[k]) - heights[i]).abs() < EPS);
assert!((dot(&normals[i], &breakpoints[k+1]) - heights[i]).abs() < EPS);
```

---

### 2.5 Action of Piecewise Linear Reeb Trajectories

For Reeb dynamics, **action equals period**:
\[
A(\gamma) = T = \sum_k \tau_k
\]

This follows from the Reeb vector definition and the contact form.

```rust
fn action_from_segment_times(segment_times: &[f64]) -> f64 {
    segment_times.iter().sum()
}

fn action_from_breakpoints_and_facets(
    breakpoints: &[[f64; 4]],
    segment_facets: &[usize],
    heights: &[f64],
) -> f64 {
    let mut total = 0.0;
    for k in 0..segment_facets.len() {
        let disp = norm(&sub(breakpoints[k + 1], breakpoints[k]));
        total += heights[segment_facets[k]] * disp / 2.0;
    }
    total
}
```

**Assertion (two computation methods agree):**
```rust
let action1 = action_from_segment_times(&segment_times);
let action2 = action_from_breakpoints_and_facets(&breakpoints, &segment_facets, &heights);
let action3 = action_of_closed_polygon(&breakpoints);  // General formula

// All three should agree for valid Reeb orbits
assert!((action1 - action2).abs() < EPS);
assert!((action1 - action3).abs() < EPS);
```

---

### 2.6 Closed Reeb Orbits

A **closed Reeb orbit** is a Reeb trajectory with \(\gamma(T) = \gamma(0)\).

```rust
struct ClosedReebOrbit {
    period: f64,                  // T = action
    breakpoints: Vec<[f64; 4]>,   // p_0, ..., p_m with p_m = p_0
    segment_facets: Vec<usize>,   // i_0, ..., i_{m-1}
    segment_times: Vec<f64>,      // τ_0, ..., τ_{m-1}
}
```

**Mathematical conditions (beyond trajectory conditions):**
1. Closure: `breakpoints[m] == breakpoints[0]`
2. `breakpoints.len() == segment_facets.len() + 1`
3. `period == Σ segment_times`

**Assertions:**
```rust
// Closure
assert!(norm(&sub(breakpoints[breakpoints.len()-1], breakpoints[0])) < EPS);

// Period = sum of times
assert!((period - segment_times.iter().sum::<f64>()).abs() < EPS);

// Period = action (from general formula)
assert!((period - action_of_closed_polygon(&breakpoints)).abs() < EPS);
```

---

### 2.7 Simple Reeb Orbits

A **simple Reeb orbit** visits each facet at most once (uses each Reeb velocity at most once).

**Source:** HK2017 Theorem 2 (Theorem \ref{simple_loop_theorem} in the paper) proves that minimum-action orbits are simple.

```rust
struct SimpleReebOrbit {
    // Same fields as ClosedReebOrbit
    period: f64,
    breakpoints: Vec<[f64; 4]>,
    segment_facets: Vec<usize>,
    segment_times: Vec<f64>,
}
```

**Mathematical conditions (beyond closed orbit conditions):**
- Simplicity: all elements of `segment_facets` are distinct

**Assertions:**
```rust
// All facets distinct
let facet_set: HashSet<_> = segment_facets.iter().collect();
assert_eq!(facet_set.len(), segment_facets.len());

// Consequence: at most F segments (F = number of facets)
assert!(segment_facets.len() <= num_facets);
```

**Significance:** The HK2017 formula and all algorithms only need to search over simple orbits.

---

### 2.8 Facet Sequences and Combinatorial Classes

A **facet sequence** \(\sigma = (i_0, i_1, \ldots, i_m)\) describes the order of facets visited.

For orbits not involving Lagrangian 2-faces, adjacency constraints apply:
1. Each consecutive pair \((i_k, i_{k+1})\) must share a non-Lagrangian 2-face
2. Flow direction must match: \(\omega(n_{i_k}, n_{i_{k+1}}) > 0\) (or the reverse, consistently)

```rust
struct FacetSequence {
    facets: Vec<usize>,  // [i_0, i_1, ..., i_m]
}

impl FacetSequence {
    fn is_valid(&self, two_faces: &[TwoFace]) -> bool {
        // Check adjacency: each consecutive pair shares a 2-face
        for k in 0..self.facets.len() - 1 {
            let i = self.facets[k];
            let j = self.facets[k + 1];
            let has_two_face = two_faces.iter()
                .any(|f| (f.i == i && f.j == j) || (f.i == j && f.j == i));
            if !has_two_face {
                return false;
            }
        }
        true
    }

    fn is_closeable(&self) -> bool {
        // Sequence [i_0, ..., i_m] is closeable if i_m = i_0 and i_{m-1}, i_1 adjacent
        // (i.e., can close back to starting 2-face)
        self.facets.len() >= 3 &&
        self.facets[self.facets.len() - 1] == self.facets[0]
        // Plus adjacency check for closing edge
    }
}
```

---

### 2.9 Tubes (Partial Trajectories)

A **tube** represents all Reeb trajectories with a fixed combinatorial class (facet sequence).

```rust
struct Tube {
    facet_sequence: Vec<usize>,   // [i_0, i_1, ..., i_k, i_{k+1}]

    // The tube starts on 2-face F_{i_0, i_1} and ends on 2-face F_{i_k, i_{k+1}}

    // In 2D trivialized coordinates of the start 2-face:
    p_start: Polygon2D,           // set of valid starting points
    p_end: Polygon2D,             // set of valid ending points

    // Affine maps describing the dynamics:
    flow_map: AffineMap2D,        // maps start point → end point
    action_func: AffineFunc,      // action as function of start point

    // Accumulated rotation
    rotation: f64,                // total rotation in turns
}

struct AffineMap2D {
    matrix: [[f64; 2]; 2],  // A
    offset: [f64; 2],       // b
    // Apply: f(x) = Ax + b
}

struct AffineFunc {
    gradient: [f64; 2],     // g
    constant: f64,          // c
    // Evaluate: f(x) = ⟨g, x⟩ + c
}
```

**Mathematical conditions:**
1. `p_start` is a convex polygon (intersection of start 2-face with tube constraints)
2. `p_end = flow_map(p_start) ∩ (end 2-face polygon)`
3. For any start point `s ∈ p_start`, there exists a unique trajectory ending at `flow_map(s)`
4. `action_func(s)` gives the action of that trajectory
5. `rotation` is constant over all trajectories in the tube (depends only on combinatorics)

**Tube initialization (root tube for 2-face \(F_{ij}\)):**
```rust
fn create_root_tube(two_face: &TwoFaceEnriched) -> Tube {
    Tube {
        facet_sequence: vec![two_face.i, two_face.j],
        p_start: two_face.polygon_2d.clone(),
        p_end: two_face.polygon_2d.clone(),
        flow_map: AffineMap2D::identity(),
        action_func: AffineFunc::zero(),
        rotation: 0.0,
    }
}
```

---

### 2.10 Tube Extension

Extending a tube by one facet transition:

```rust
fn extend_tube(
    tube: &Tube,
    next_facet: usize,
    polytope_data: &PolytopeData,
) -> Option<Tube> {
    let current_end_facet = tube.facet_sequence[tube.facet_sequence.len() - 1];
    let two_face = polytope_data.get_two_face(current_end_facet, next_facet)?;

    // Compute flow across the facet
    let (phi, time_func) = compute_facet_flow(current_end_facet, next_facet, polytope_data);

    // New endpoint set
    let new_p_end = intersect_polygons(
        &apply_affine_map(&phi, &tube.p_end),
        &two_face.polygon_2d,
    );

    if new_p_end.is_empty() {
        return None;  // No valid trajectories
    }

    Some(Tube {
        facet_sequence: [&tube.facet_sequence[..], &[next_facet]].concat(),
        p_start: tube.p_start.clone(),
        p_end: new_p_end,
        flow_map: compose_affine(&phi, &tube.flow_map),
        action_func: add_affine_funcs(&tube.action_func, &compose_with_map(&time_func, &tube.flow_map)),
        rotation: tube.rotation + two_face.rotation_number(),
    })
}
```

---

### 2.11 Tube Closure (Finding Periodic Orbits)

A tube is **closeable** if its facet sequence returns to the starting 2-face.

To find closed orbits, solve for fixed points of the flow map:
\[
\psi(s) = s \quad \Leftrightarrow \quad (A - I) s = -b
\]

```rust
fn find_closed_orbits(tube: &Tube) -> Vec<(f64, [f64; 2])> {
    // Solve (A - I) s = -b
    let a_minus_i = [
        [tube.flow_map.matrix[0][0] - 1.0, tube.flow_map.matrix[0][1]],
        [tube.flow_map.matrix[1][0], tube.flow_map.matrix[1][1] - 1.0],
    ];
    let neg_b = [-tube.flow_map.offset[0], -tube.flow_map.offset[1]];

    let det = a_minus_i[0][0] * a_minus_i[1][1] - a_minus_i[0][1] * a_minus_i[1][0];

    if det.abs() < EPS {
        // Degenerate: line or plane of fixed points
        // Handle separately...
        return find_fixed_point_set(tube);
    }

    // Unique fixed point
    let s = [
        (a_minus_i[1][1] * neg_b[0] - a_minus_i[0][1] * neg_b[1]) / det,
        (-a_minus_i[1][0] * neg_b[0] + a_minus_i[0][0] * neg_b[1]) / det,
    ];

    // Check if fixed point is in p_start (the valid region)
    if !point_in_polygon(&s, &tube.p_start) {
        return vec![];
    }

    let action = evaluate_affine_func(&tube.action_func, &s);
    vec![(action, s)]
}
```

**Assertions:**
```rust
// Fixed point satisfies flow_map(s) = s
let s_mapped = apply_affine_map(&tube.flow_map, &fixed_point);
assert!(norm_2d(&sub_2d(s_mapped, fixed_point)) < EPS);

// Fixed point is in the valid start region
assert!(point_in_polygon(&fixed_point, &tube.p_start));
```

---

### 2.12 Reconstruction: 2D Coordinates to 4D Orbit

Given a closed orbit in 2D trivialized coordinates, reconstruct the 4D orbit:

```rust
fn reconstruct_4d_orbit(
    fixed_point_2d: [f64; 2],
    tube: &Tube,
    polytope_data: &PolytopeData,
) -> ClosedReebOrbit {
    // Start from the 2D fixed point on the start 2-face
    let start_two_face = polytope_data.get_two_face(
        tube.facet_sequence[0],
        tube.facet_sequence[1],
    );

    // Convert 2D → 4D via barycentric interpolation
    let start_4d = untrivialize_point(
        fixed_point_2d,
        &start_two_face,
    );

    // Trace through each facet to get breakpoints
    let mut breakpoints = vec![start_4d];
    let mut current_2d = fixed_point_2d;

    for k in 1..tube.facet_sequence.len() - 1 {
        let facet = tube.facet_sequence[k];
        let (phi, _) = get_facet_flow(k, tube, polytope_data);
        current_2d = apply_affine_map_point(&phi, &current_2d);

        let two_face = polytope_data.get_two_face(
            tube.facet_sequence[k],
            tube.facet_sequence[k + 1],
        );
        let point_4d = untrivialize_point(current_2d, &two_face);
        breakpoints.push(point_4d);
    }

    breakpoints.push(start_4d);  // Close the orbit

    // Compute segment times and facets
    // ...

    ClosedReebOrbit { period, breakpoints, segment_facets, segment_times }
}
```

---

### 2.13 Validity Checks for Reeb Orbits

Comprehensive validation for computed orbits:

```rust
impl ClosedReebOrbit {
    fn validate(&self, hrep: &PolytopeHRep) -> Result<(), ValidationError> {
        // 1. Closure
        if norm(&sub(self.breakpoints.last().unwrap(), &self.breakpoints[0])) > EPS {
            return Err(ValidationError::NotClosed);
        }

        // 2. All breakpoints on boundary
        for (k, p) in self.breakpoints.iter().enumerate() {
            if !is_on_boundary(*p, hrep) {
                return Err(ValidationError::BreakpointNotOnBoundary(k));
            }
        }

        // 3. Segments lie on claimed facets
        for k in 0..self.segment_facets.len() {
            let i = self.segment_facets[k];
            let p_start = self.breakpoints[k];
            let p_end = self.breakpoints[k + 1];

            if (dot(&hrep.normals[i], &p_start) - hrep.heights[i]).abs() > EPS {
                return Err(ValidationError::SegmentNotOnFacet(k, "start"));
            }
            if (dot(&hrep.normals[i], &p_end) - hrep.heights[i]).abs() > EPS {
                return Err(ValidationError::SegmentNotOnFacet(k, "end"));
            }
        }

        // 4. Velocities match Reeb vectors
        for k in 0..self.segment_facets.len() {
            let i = self.segment_facets[k];
            let displacement = sub(self.breakpoints[k + 1], self.breakpoints[k]);
            let velocity = scale(1.0 / self.segment_times[k], displacement);
            let reeb = scale(2.0 / hrep.heights[i], complex_structure(hrep.normals[i]));

            if norm(&sub(velocity, reeb)) > EPS * norm(&reeb) {
                return Err(ValidationError::VelocityMismatch(k));
            }
        }

        // 5. Period = sum of times = action
        let time_sum: f64 = self.segment_times.iter().sum();
        if (self.period - time_sum).abs() > EPS {
            return Err(ValidationError::PeriodMismatch);
        }

        let action = action_of_closed_polygon(&self.breakpoints);
        if (self.period - action).abs() > EPS * self.period {
            return Err(ValidationError::ActionMismatch);
        }

        Ok(())
    }
}
```

---

## 3. Algorithms

### 3.1 Algorithm Applicability Summary

| Algorithm | Domain | Complexity | Notes |
|-----------|--------|------------|-------|
| Billiard | Lagrangian products \(K_1 \times K_2\) | \(O(n_1^3 \times n_2^3)\) | Most reliable |
| HK2017 | All polytopes | \(O(F!)\) | Limited to ~10 facets |
| Tube | Non-Lagrangian polytopes | \(O(F! \times \text{poly})\) | Requires no Lagrangian 2-faces |

### 3.2 Billiard Algorithm (for Lagrangian Products)

**Source:** Rudolf 2022, "The Minkowski Billiard Characterization of the EHZ Capacity"

**Input:** Lagrangian product \(K = K_1 \times K_2\) where \(K_1, K_2 \subset \mathbb{R}^2\) are convex polygons.

**Output:** \(c_{\text{EHZ}}(K)\) = minimum T-length of closed billiard trajectory.

**Theorem (Rudolf 2022, Thm 4):** For 2D polygon factors, optimal trajectory has at most 3 bounces.

**Algorithm:**
```rust
fn billiard_capacity(K: LagrangianProductPolytope) -> f64 {
    let mut best_action = f64::INFINITY;

    // Enumerate all 3-bounce combinatorics
    for eq in all_edge_triples(K.K1.num_edges) {
        for ep in all_edge_triples(K.K2.num_edges) {
            // Solve LP for this edge combination
            if let Some(action) = solve_billiard_lp(&K, &eq, &ep) {
                if action > EPS && action < best_action {
                    best_action = action;
                }
            }
        }
    }

    best_action
}
```

**LP Variables (per 3-bounce trajectory):**
- \(m_{q,k} \in [0,1]\): position parameter on edge \(k\) of \(K_1\)
- \(m_{p,k} \in [0,1]\): position parameter on edge \(k\) of \(K_2\)
- \(t_{q,k}, t_{p,k} \geq 0\): segment times

**Constraints:**
- Reeb velocity: displacement = time × Reeb vector
- Closure: trajectory returns to start

**Objective:** Minimize total time \(T = \sum_k (t_{q,k} + t_{p,k})\)

**Degeneracy:** Solutions with action ≈ 0 are point orbits; discard them.

---

### 3.3 Haim-Kislev 2017 Quadratic Programming

**Source:** Haim-Kislev 2017, "On the Symplectic Size of Convex Polytopes"

**Input:** Any polytope \(K\) with \(F\) facets.

**Output:** \(c_{\text{EHZ}}(K) = \frac{1}{2} \cdot [\max_{\sigma, \beta} Q(\sigma, \beta)]^{-1}\)

**Q-function:**
\[
Q(\sigma, \beta) = \sum_{j < i} \beta_{\sigma(i)} \beta_{\sigma(j)} \omega(n_{\sigma(i)}, n_{\sigma(j)})
\]

**Constraints on \(\beta\):**
- \(\beta_i \geq 0\) (non-negative)
- \(\sum_i \beta_i h_i = 1\) (height normalization)
- \(\sum_i \beta_i n_i = 0\) (closure: 4 equations in \(\mathbb{R}^4\))

**Algorithm:**
```rust
fn hk2017_capacity(K: &PolytopeHRep) -> f64 {
    let mut best_q = 0.0;

    for sigma in permutations(0..K.num_facets) {
        // For each permutation, solve the QP
        let q_max = solve_q_maximization(&K, &sigma);
        if q_max > best_q {
            best_q = q_max;
        }
    }

    0.5 / best_q
}
```

**CRITICAL WARNING:** Q is indefinite (neither convex nor concave). The maximum may occur at:
- Vertices (0D faces) of the feasible polytope
- Edges (1D faces)
- Higher-dimensional faces

A complete implementation requires a global QCQP solver. Checking only vertices is **incomplete**.

---

### 3.4 Tube Algorithm (Branch and Bound)

**Source:** Chaidez-Hutchings 2021, "Computing Reeb Dynamics on Polytopes"

**Input:** Polytope with **no Lagrangian 2-faces** (i.e., \(\omega(n_i, n_j) \neq 0\) for all adjacent facet pairs).

**Output:** Minimum-action closed Reeb orbit.

**Algorithm:**
```rust
fn tube_capacity(K: &PolytopeHRep) -> Result<f64, Error> {
    let data = preprocess_polytope(K)?;  // Compute 2-faces, rotations, trivializations

    if data.has_lagrangian_two_faces() {
        return Err(Error::LagrangianTwoFaces);
    }

    let mut best_action = f64::INFINITY;
    let mut worklist = PriorityQueue::new();  // By action lower bound

    // Initialize: one root tube per 2-face
    for two_face in &data.two_faces {
        worklist.push(create_root_tube(two_face));
    }

    // Branch and bound
    while let Some(tube) = worklist.pop() {
        if tube.action_lower_bound() >= best_action {
            continue;  // Prune
        }

        for extension in tube.get_extensions(&data) {
            match extension {
                Extension::Closed(orbit) => {
                    if orbit.action < best_action {
                        best_action = orbit.action;
                    }
                }
                Extension::Open(new_tube) => {
                    if new_tube.rotation <= 2.0 + EPS_ROTATION {
                        worklist.push(new_tube);
                    }
                }
            }
        }
    }

    Ok(best_action)
}
```

**Pruning rules:**
1. **Empty tube:** No valid starting points remain
2. **Action bound:** Minimum action in tube exceeds best found
3. **Rotation bound:** Total rotation > 2 turns (CH2021 Prop 1.10)

**Closure condition:** Facet sequence returns to starting 2-face, and flow map has a fixed point in the valid region.

---

## 4. Test Cases and Verification Properties

This section lists mathematical properties that tests should verify. If any test fails, the code contains a bug (does not correspond to the mathematical "proof").

### 4.1 Ground Truth Capacity Values

| Polytope | \(c_{\text{EHZ}}\) | Source | Notes |
|----------|-----------|--------|-------|
| Tesseract \([-1,1]^4\) | 4.0 | HK2017 Ex 4.6 | Primary test case |
| Rectangle \(2 \times 1\) product | 1.0 | Scaling | |
| Triangle × Triangle (r=1) | 1.5 | Computational | Circumradius 1 |
| Pentagon × RotatedPentagon | 3.441 | HK-O 2024 Prop 1 | Counterexample to Viterbo |
| 4-Simplex | 0.25 | Y. Nir 2013 | Non-Lagrangian product |

**Test pattern:**
```rust
#[test]
fn test_tesseract_capacity() {
    let K = tesseract();
    let result = compute_capacity(&K);
    assert!((result.capacity - 4.0).abs() < EPS);
}
```

---

### 4.2 Capacity Axioms

**4.2.1 Scaling:** \(c(\lambda K) = \lambda^2 c(K)\)

```rust
#[test]
fn test_scaling_axiom() {
    let K = tesseract();
    let lambda = 2.0;
    let K_scaled = scale_polytope(&K, lambda);

    let c_K = compute_capacity(&K).capacity;
    let c_scaled = compute_capacity(&K_scaled).capacity;

    assert!((c_scaled - lambda * lambda * c_K).abs() < EPS * c_scaled);
}
```

**4.2.2 Monotonicity:** \(K \subseteq L \Rightarrow c(K) \leq c(L)\)

```rust
#[test]
fn test_monotonicity_axiom() {
    let K = tesseract();
    let L = scale_polytope(&K, 1.5);  // K ⊂ L

    let c_K = compute_capacity(&K).capacity;
    let c_L = compute_capacity(&L).capacity;

    assert!(c_K <= c_L + EPS);
}
```

**4.2.3 Symplectomorphism Invariance:** \(c(AK) = c(K)\) for \(A \in \mathrm{Sp}(4)\)

```rust
#[test]
fn test_symplectic_invariance() {
    let K = tesseract();

    // Test multiple Sp(4) elements: rotations, shears, exchanges
    for A in sample_sp4_elements() {
        let K_transformed = apply_symplectomorphism(&K, &A);
        let c_K = compute_capacity(&K).capacity;
        let c_transformed = compute_capacity(&K_transformed).capacity;

        assert!((c_K - c_transformed).abs() < EPS * c_K,
            "Symplectic invariance failed for {:?}", A);
    }
}
```

**Sp(4) generators to test:**
- Block rotations: \(R(\theta) \oplus R(\phi)\)
- Shears: \((q, p) \mapsto (q, p + Sq)\) for symmetric \(S\)
- Symplectic exchanges: swap \((q_1, p_1) \leftrightarrow (q_2, p_2)\)

---

### 4.3 Orbit Validity Tests

**4.3.1 Breakpoints on boundary:**
```rust
fn test_breakpoints_on_boundary(orbit: &ClosedReebOrbit, K: &PolytopeHRep) {
    for p in &orbit.breakpoints {
        assert!(is_on_boundary(*p, K), "Breakpoint not on boundary");
    }
}
```

**4.3.2 Segments on facets:**
```rust
fn test_segments_on_facets(orbit: &ClosedReebOrbit, K: &PolytopeHRep) {
    for k in 0..orbit.segment_facets.len() {
        let i = orbit.segment_facets[k];
        let p0 = orbit.breakpoints[k];
        let p1 = orbit.breakpoints[k + 1];

        // Both endpoints on the claimed facet
        assert!((dot(&K.normals[i], &p0) - K.heights[i]).abs() < EPS);
        assert!((dot(&K.normals[i], &p1) - K.heights[i]).abs() < EPS);
    }
}
```

**4.3.3 Velocities match Reeb vectors (differential inclusion):**
```rust
fn test_reeb_velocity(orbit: &ClosedReebOrbit, K: &PolytopeHRep) {
    for k in 0..orbit.segment_facets.len() {
        let i = orbit.segment_facets[k];
        let displacement = sub(orbit.breakpoints[k + 1], orbit.breakpoints[k]);
        let velocity = scale(1.0 / orbit.segment_times[k], displacement);
        let reeb = scale(2.0 / K.heights[i], complex_structure(K.normals[i]));

        assert!(norm(&sub(velocity, reeb)) < EPS * norm(&reeb),
            "Velocity on segment {} doesn't match Reeb vector", k);
    }
}
```

**4.3.4 Orbit closure:**
```rust
fn test_orbit_closure(orbit: &ClosedReebOrbit) {
    let first = orbit.breakpoints[0];
    let last = orbit.breakpoints[orbit.breakpoints.len() - 1];
    assert!(norm(&sub(first, last)) < EPS, "Orbit not closed");
}
```

**4.3.5 Action = period = sum of times:**
```rust
fn test_action_consistency(orbit: &ClosedReebOrbit) {
    let time_sum: f64 = orbit.segment_times.iter().sum();
    let action = action_of_closed_polygon(&orbit.breakpoints);

    assert!((orbit.period - time_sum).abs() < EPS);
    assert!((orbit.period - action).abs() < EPS * orbit.period);
}
```

---

### 4.4 Algorithm Agreement

On their common domain (Lagrangian products), different algorithms should agree:

```rust
#[test]
fn test_billiard_hk2017_agreement() {
    for K in sample_lagrangian_products() {
        let c_billiard = billiard_capacity(&K);
        let c_hk2017 = hk2017_capacity(&K.to_hrep());

        let rel_error = (c_billiard - c_hk2017).abs() / c_billiard;
        assert!(rel_error < 0.01, "Algorithms disagree: billiard={}, hk2017={}",
            c_billiard, c_hk2017);
    }
}
```

---

### 4.5 Geometric Foundation Tests

**4.5.1 Symplectic form properties:**
```rust
#[test]
fn test_symplectic_form_properties() {
    // Antisymmetry
    assert!((symplectic_form(u, v) + symplectic_form(v, u)).abs() < EPS);

    // Bilinearity
    assert!((symplectic_form(add(u, v), w) - symplectic_form(u, w) - symplectic_form(v, w)).abs() < EPS);

    // Standard basis values
    assert!((symplectic_form([1,0,0,0], [0,0,1,0]) - 1.0).abs() < EPS);  // ω(e1, e3) = 1
    assert!((symplectic_form([0,1,0,0], [0,0,0,1]) - 1.0).abs() < EPS);  // ω(e2, e4) = 1
    assert!((symplectic_form([1,0,0,0], [0,1,0,0])).abs() < EPS);        // ω(e1, e2) = 0
}
```

**4.5.2 Quaternion relations:**
```rust
#[test]
fn test_quaternion_relations() {
    let v = random_unit_vector();

    // J² = K² = -I
    assert!(norm(&add(J(J(v)), v)) < EPS);
    assert!(norm(&add(K(K(v)), v)) < EPS);

    // JK = -KJ
    assert!(norm(&add(J(K(v)), K(J(v)))) < EPS);
}
```

**4.5.3 Transition matrix is symplectic:**
```rust
#[test]
fn test_transition_matrix_symplectic() {
    for two_face in &polytope_data.two_faces {
        let psi = two_face.transition_matrix;

        // det(ψ) = 1
        let det = psi[0][0] * psi[1][1] - psi[0][1] * psi[1][0];
        assert!((det - 1.0).abs() < EPS);

        // ψᵀ J₂ ψ = J₂
        // (This is equivalent to det = 1 for 2×2 matrices)
    }
}
```

**4.5.4 Rotation number in valid range:**
```rust
#[test]
fn test_rotation_number_range() {
    for two_face in &polytope_data.two_faces {
        if !two_face.is_lagrangian() {
            let rho = two_face.rotation_number();
            assert!(rho > 0.0 && rho < 0.5,
                "Rotation {} not in (0, 0.5)", rho);
        }
    }
}
```

---

### 4.6 Tube Algorithm Specific Tests

**4.6.1 Flow map consistency:**
```rust
fn test_tube_flow_map(tube: &Tube, start_point: [f64; 2]) {
    // Trace the trajectory step by step
    let traced_end = trace_trajectory_stepwise(tube, start_point);

    // Compare with flow map
    let mapped_end = apply_affine_map(&tube.flow_map, &start_point);

    assert!(norm_2d(&sub_2d(traced_end, mapped_end)) < EPS);
}
```

**4.6.2 Action function consistency:**
```rust
fn test_tube_action_func(tube: &Tube, start_point: [f64; 2]) {
    // Trace trajectory and sum segment times
    let traced_action = trace_and_sum_action(tube, start_point);

    // Compare with action function
    let computed_action = evaluate_affine_func(&tube.action_func, &start_point);

    assert!((traced_action - computed_action).abs() < EPS);
}
```

**4.6.3 Closed orbit is actually closed:**
```rust
fn test_closed_orbit_is_fixed_point(orbit_2d: [f64; 2], tube: &Tube) {
    let mapped = apply_affine_map(&tube.flow_map, &orbit_2d);
    assert!(norm_2d(&sub_2d(orbit_2d, mapped)) < EPS,
        "Claimed closed orbit is not a fixed point of flow map");
}
```

---

### 4.7 Polytope Data Consistency

**4.7.1 H-rep ↔ V-rep consistency:**
```rust
fn test_hrep_vrep_consistency(K: &PolytopeRepEnriched) {
    // Every vertex satisfies all inequalities
    for v in &K.vertices {
        for (n, &h) in K.normals.iter().zip(&K.heights) {
            assert!(dot(n, v) <= h + EPS);
        }
    }

    // Every vertex is tight on exactly dim=4 facets (for simple polytopes)
    for v in &K.vertices {
        let tight_count = K.normals.iter().zip(&K.heights)
            .filter(|(n, &h)| (dot(n, v) - h).abs() < EPS)
            .count();
        assert!(tight_count >= 4, "Vertex on fewer than 4 facets");
    }
}
```

**4.7.2 2-face enumeration correctness:**
```rust
fn test_two_face_enumeration(data: &PolytopeData) {
    for two_face in &data.two_faces {
        // 2-face vertices are on both facets
        for v in &two_face.vertices_4d {
            assert!((dot(&data.normals[two_face.i], v) - data.heights[two_face.i]).abs() < EPS);
            assert!((dot(&data.normals[two_face.j], v) - data.heights[two_face.j]).abs() < EPS);
        }

        // Lagrangian classification is correct
        let omega = symplectic_form(data.normals[two_face.i], data.normals[two_face.j]);
        assert_eq!(omega.abs() < EPS_LAGRANGIAN, two_face.is_lagrangian);
    }
}
```

---

### 4.8 Test Fixture Definitions

**Tesseract:**
```rust
fn tesseract() -> PolytopeHRep {
    PolytopeHRep {
        normals: vec![
            [1.0, 0.0, 0.0, 0.0], [-1.0, 0.0, 0.0, 0.0],
            [0.0, 1.0, 0.0, 0.0], [0.0, -1.0, 0.0, 0.0],
            [0.0, 0.0, 1.0, 0.0], [0.0, 0.0, -1.0, 0.0],
            [0.0, 0.0, 0.0, 1.0], [0.0, 0.0, 0.0, -1.0],
        ],
        heights: vec![1.0; 8],
    }
}
```

**Triangle × Triangle (equilateral, circumradius 1):**
```rust
fn triangle_product() -> LagrangianProductPolytope {
    let angles = [0.0, 2.0 * PI / 3.0, 4.0 * PI / 3.0];
    let vertices: Vec<[f64; 2]> = angles.iter()
        .map(|&a| [a.cos(), a.sin()])
        .collect();

    // Compute normals (outward, perpendicular to edges)
    // ...

    LagrangianProductPolytope {
        K1: /* triangle */,
        K2: /* same triangle */,
    }
}
```

**Pentagon × RotatedPentagon (HK-O counterexample):**
```rust
fn hko_counterexample() -> LagrangianProductPolytope {
    let angles: Vec<f64> = (0..5).map(|i| 2.0 * PI * i as f64 / 5.0).collect();

    let pentagon_vertices: Vec<[f64; 2]> = angles.iter()
        .map(|&a| [a.cos(), a.sin()])
        .collect();

    let rotated_vertices: Vec<[f64; 2]> = angles.iter()
        .map(|&a| [(a + PI/2.0).cos(), (a + PI/2.0).sin()])
        .collect();

    // Expected capacity: 2 * cos(π/10) * (1 + cos(π/5)) ≈ 3.4409548
    LagrangianProductPolytope {
        K1: polygon_from_vertices(pentagon_vertices),
        K2: polygon_from_vertices(rotated_vertices),
    }
}
```

---

## References

### Primary Sources (Algorithms)

- **CH2021:** Chaidez-Hutchings, "Computing Reeb Dynamics on Four-Dimensional Convex Polytopes" (arXiv:2102.07401)
- **HK2017:** Haim-Kislev, "On the Symplectic Size of Convex Polytopes" (arXiv:1712.03494)
- **Rudolf 2022:** "The Minkowski Billiard Characterization of the EHZ-Capacity" (arXiv:2203.01718)

### Primary Sources (Ground Truth Values)

- **HK-O 2024:** Haim-Kislev & Ostrover, "A Counterexample to Viterbo's Conjecture" (arXiv:2405.16513)
- **Y. Nir 2013:** "On Closed Characteristics and Billiards in Convex Bodies" (thesis, Tel Aviv University)

### Textbooks

- **Hofer-Zehnder 1994:** "Symplectic Invariants and Hamiltonian Dynamics"
- **Schneider 2014:** "Convex Bodies: The Brunn-Minkowski Theory"
- **McDuff-Salamon 2017:** "Introduction to Symplectic Topology"
