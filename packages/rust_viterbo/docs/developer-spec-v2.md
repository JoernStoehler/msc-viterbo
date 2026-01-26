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
   - 1.1 Polytope Representation (H-rep and V-rep)
   - 1.2 Facets (3-faces)
   - 1.3 Reeb Vectors
   - 1.4 Symplectic Form
   - 1.5 Two-Faces and Adjacency
   - 1.6 Lagrangian vs Non-Lagrangian 2-Faces
   - 1.7 Flow Direction on Non-Lagrangian 2-Faces
   - 1.8 Lagrangian Product Structure
   - 1.9 Quaternion Structure
   - 1.10 Trivialization
   - 1.11 Transition Matrices
   - 1.12 Rotation Number
   - 1.13 Support Function and Polar Body
   - 1.14 Trivialized 2-Face Polygons
   - 1.15 Edge and Vertex Incidence
   - 1.16 Constants and Tolerances

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
- Viterbo's conjecture (disproven in 2024) predicted \(c_{\text{EHZ}}(K)^2 \leq 2 \cdot \text{Vol}(K)\)
- The HK-O 2024 counterexample (pentagon × rotated pentagon) has \(c^2 / (2 \cdot \text{Vol}) \approx 1.047 > 1\)

### Capacity Axioms (What Tests Should Verify)

1. **Scaling:** \(c(\lambda K) = \lambda^2 \cdot c(K)\) for \(\lambda > 0\)
2. **Monotonicity:** \(K \subseteq L \Rightarrow c(K) \leq c(L)\)
3. **Symplectic invariance:** \(c(AK+b) = c(K)\) for \(A \in \text{Sp}(4)\) and \(b \in \mathbb{R}^4\)
4. **Normalization:** \(c(B^4) = c(Z^4) = \pi\) (ball and cylinder)

The axioms also imply:

5. **Continuity:** If \(K_j \to K\) in Hausdorff metric, then \(c(K_j) \to c(K)\)

### Document Structure

- **Part 1:** Data about the polytope \(K\) — all derived quantities needed by algorithms
- **Part 2:** Data about Reeb trajectories and orbits — representations and validity conditions
- **Part 3:** Algorithms — Billiard, HK2017, Tube
- **Part 4:** Test cases — properties that detect bugs when code diverges from math

### Document Style

- We outsource mathematical proofs to the thesis or literature.
- We make our mathematical definitions and propositions explicit and precise. We need to be extra careful here since Rust code has a less strong type system than "Mathematics" itself, and we need to manually track the missing information.
- We give Rust structures and functions to represent the mathematical definitions and propositions, though of course Rust is lossy as it has no dependent types or proof system. We do suggest assertions, function signatures that can be filled in by a math-savvy programmer, and unit tests as ways to confirm computationally that the Rust code corresponds to the math proofs. We also suggest code comments to keep track of type information, in the computer science sense of preconditions and postconditions and invariants, and in the type system sense of dependent types and proposition types that we know are occupied even without any automated proof checker using these code comments.
- We use progressive disclosure, and we don't prescribe how the programmers arrange the presented Rust snippets into actual executable code, e.g. we don't prescribe what inputs and outputs the final API will use. This is left to software architects. We focus instead on the internal logic, i.e. on how to keep Rust code close to the math. 

### Unstated Assertions and Code Style

We have several silent assertions that apply everywhere and which we don't repeat. We suggest to write code such that these silent assertions "blow up" and get caught eventually, or even "panic" and just interrupt code. It's not expected / best practice to manually insert checks for these silent assertions everywhere, since that's a waste of compute and hinders code clarity.

- **Floating point arithmetic:** All floating point operations are assumed to work without overflow, underflow, or NaNs, unless otherwise specified. All floating point comparisons are to be done with tolerance parameters. 
- **Conservative branching when using floating point comparisons:** Since we are ultimately doing a minimum search, these tolerances should be signed such that the true minimum is not accidentally rejected, and that inadmissible minima can be rejected near the end in a separate validation step. If designing a variant of the algorithms presented here that is conservative in this regard is too difficult, then a good fallback is to allow a return value that indicates uncertainty about the validity of the result, i.e. that maybe an inadmissible minimum was accepted which is lower than the true minimum. If that still is too difficult, then a warning that something may be wrong in either direction is useful. If that still is too difficult, then at least we will have good documentation that informs API users of the danger that the result is not just numerically rounded, but in fact may be combinatorically wrong.
- **Functional Programming:** We use functional programming best practices to avoid dealing with Rust's borrow checker.
- **Linear Algebra:** We use `nalgebra` for vectors and matrices (`Vector4<f64>`, `Vector2<f64>`, `Matrix2<f64>`, `Matrix4<f64>`). This enables natural mathematical notation like `J_MATRIX * n` for matrix-vector products, `v.dot(&w)` for inner products, and `v.norm()` for norms.
- **No concurrency:** We are satisfied with single-threaded library code, though of course the tests and later experiments can be run embarrassingly parallel.
- **Debug-Asserts:** The production code is optimized for speed, the debug code is optimized for catching any bugs. We suggest to use `debug_assert!` for assertions in performance critical code, where performance criticality is determined by profiling and not by guesswork.
- **Unit tests in Rust and Python:** Some propositions require input with special properties, e.g. when we want to assert that an algorithm returns the literature values of the capacity for certain polytopes. In such cases we use unit tests, which if fast enough can just be run every time, and if too costly can be run selectively. Especially costly / complex-to-setup unit tests may even be Python tests rather than Rust tests. Similarly, some assertions are too costly to run for all function calls in the debug build, e.g. because they'd be run for all unit tests, and so despite being suitable to be run for many inputs, we only activate them / we move them outside the function into select unit tests. This is all meant in addition to the other python tests that cover actual python code, which this document does not talk about. Python unit tests are perhaps suitable for infrequent expensive tests that are run selectively, while Rust unit tests often are more suitable inexpensive tests that can be run every time. In total, the "default" test suite (Rust only) should be less than 1 minute ideally. This bound can be edited and relaxed / sharpened with Project Owner permission. Current agreed target is 1 minute.
Select tests can be longer, but anything above 10 minutes incurs high friction costs for developers and is to be avoided if possible, and must be documented clearly. Current tests exceeding 10 minutes: none.

---

## 1. Data about the Polytope K

Throughout this document, \(K \subset \mathbb{R}^4\) is a fixed polytope with \(0 \in \mathrm{int}(K)\).

A **polytope** is equivalently:
- The convex hull of finitely many points, with nonempty interior
- The bounded intersection of finitely many half-spaces, with nonempty interior

We work in standard symplectic \(\mathbb{R}^4\) with coordinates \((q_1, q_2, p_1, p_2)\).

---

### 1.1 Polytope Representation (H-rep and V-rep)

A polytope can be represented equivalently as:
- **H-representation:** Intersection of half-spaces \(K = \bigcap_i \{ x : \langle n_i, x \rangle \leq h_i \}\)
- **V-representation:** Convex hull of vertices \(K = \mathrm{conv}(\{v_0, \ldots, v_{V-1}\})\)

We take H-rep as input (compact, algorithms use facet normals directly) and compute V-rep for validation.

```rust
use nalgebra::{Vector4, Vector2, Matrix2};

struct PolytopeHRep {
    normals: Vec<Vector4<f64>>,   // unit outward normals
    heights: Vec<f64>,            // h_i > 0 (since 0 ∈ int(K))
}

struct PolytopeVRep {
    vertices: Vec<Vector4<f64>>,
}

fn vertex_enumeration(hrep: &PolytopeHRep) -> PolytopeVRep;  // e.g., double description method
```

**Validation** (requires both representations):

```rust
fn validate_polytope(hrep: &PolytopeHRep, vrep: &PolytopeVRep) -> Result<(), ValidationError> {
    // 1. Basic H-rep checks
    assert!(hrep.normals.len() == hrep.heights.len());
    assert!(hrep.normals.iter().all(|n| (n.norm() - 1.0).abs() < EPS));
    assert!(hrep.heights.iter().all(|&h| h > 0.0));  // 0 in interior

    // 2. No duplicate half-spaces
    for i in 0..hrep.normals.len() {
        for j in (i+1)..hrep.normals.len() {
            assert!(!(
                (hrep.heights[i] - hrep.heights[j]).abs() < EPS &&
                (hrep.normals[i] - hrep.normals[j]).norm() < EPS
            ), "half-spaces {} and {} are duplicates", i, j);
        }
    }

    // 3. Vertices satisfy all constraints and lie on boundary
    for v in &vrep.vertices {
        assert!(hrep.normals.iter().zip(&hrep.heights)
            .all(|(n, &h)| n.dot(v) <= h + EPS));
        assert!(hrep.normals.iter().zip(&hrep.heights)
            .any(|(n, &h)| (n.dot(v) - h).abs() < EPS));
    }

    // 4. Non-redundancy: every half-space has ≥4 vertices (3D facet in 4D)
    for i in 0..hrep.normals.len() {
        let count = vrep.vertices.iter()
            .filter(|v| (hrep.normals[i].dot(v) - hrep.heights[i]).abs() < EPS)
            .count();
        assert!(count >= 4, "facet {} is redundant or degenerate", i);
    }

    Ok(())
}
```

**Boundedness:** Vertex enumeration implicitly checks boundedness (unbounded polytopes have no vertices or infinitely many). Alternatively, check that normals positively span ℝ⁴ via LP feasibility: "∃c ≠ 0 with ⟨n_i, c⟩ ≥ 0 ∀i" means unbounded.

**Derived quantities:**
```rust
let num_facets: usize = hrep.normals.len();
let num_vertices: usize = vrep.vertices.len();
```

---

### 1.2 Facets (3-faces)

A **facet** \(F_i\) is the intersection of \(K\) with the \(i\)-th bounding hyperplane:
\[
F_i = K \cap \{ x : \langle n_i, x \rangle = h_i \}
\]

Facets are 3-dimensional convex polytopes. We index them by \(i \in \{0, \ldots, F-1\}\).

```rust
struct Facet {
    index: usize,              // i
    normal: Vector4<f64>,      // n_i (outward unit normal)
    height: f64,               // h_i
    vertices: Vec<usize>,      // indices into global vertex list (vertices where ⟨n_i, v⟩ = h_i)
}
```

**Assertion:** Each facet has ≥4 vertices (3D polytope in 4D).

---

### 1.3 Reeb Vectors

The **Reeb vector** on facet \(F_i\) is the direction of the Reeb flow:
\[
R_i = \frac{2}{h_i} J n_i
\]

**Derivation** (see thesis `math/05-reeb-dynamics.tex`): For the contact form \(\alpha = \lambda|_{\partial K}\) where \(\lambda = \frac{1}{2}(p \, dq - q \, dp)\), the Reeb vector \(R\) satisfies \(\alpha(R) = 1\) and \(\iota_R d\alpha = 0\). At a point \(x\) on facet \(F_i\) with outward normal \(n_i\), this gives \(R(x) = \frac{2}{\langle x, n_i \rangle} J n_i\). Since points on \(F_i\) satisfy \(\langle x, n_i \rangle = h_i\), we have \(R_i = \frac{2}{h_i} J n_i\).

Here \(J\) is the standard complex structure:
\[
J(q_1, q_2, p_1, p_2) = (-p_1, -p_2, q_1, q_2)
\]

```rust
use nalgebra::{Vector4, Vector2, Matrix2, Matrix4};

/// The standard almost complex structure (symplectic J matrix).
/// This is QUAT_I in CH2021's quaternion notation (see §1.9).
/// Used for symplectic form and Reeb vectors.
const J_MATRIX: Matrix4<f64> = QUAT_I;

let reeb_vectors: Vec<Vector4<f64>> = (0..num_facets)
    .map(|i| (J_MATRIX * normals[i]) * (2.0 / heights[i]))
    .collect();
```

**Assertions:**
```rust
// Reeb vectors are perpendicular to their facet normal
assert!(reeb_vectors.iter().zip(&normals)
    .all(|(r, n)| r.dot(n).abs() < EPS));

// Reeb vectors have magnitude 2/h_i
assert!(reeb_vectors.iter().zip(&heights)
    .all(|(r, &h)| (r.norm() - 2.0/h).abs() < EPS));
```

---

### 1.4 Symplectic Form

The **symplectic form** \(\omega\) on \(\mathbb{R}^4\):
\[
\omega(x, y) = \langle Jx, y \rangle = q_1 p_1' + q_2 p_2' - p_1 q_1' - p_2 q_2'
\]

```rust
fn symplectic_form(x: &Vector4<f64>, y: &Vector4<f64>) -> f64 {
    (J_MATRIX * x).dot(y)
}
```

**Properties:**
- Antisymmetric: \(\omega(x, y) = -\omega(y, x)\)
- Non-degenerate: \(\omega(x, y) = 0\) for all \(y\) implies \(x = 0\)

**Standard basis pairings:**
```rust
let e1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
let e2 = Vector4::new(0.0, 1.0, 0.0, 0.0);
let e3 = Vector4::new(0.0, 0.0, 1.0, 0.0);
let e4 = Vector4::new(0.0, 0.0, 0.0, 1.0);

assert_eq!(symplectic_form(&e1, &e3),  1.0);  // omega(e_1, e_3) = 1
assert_eq!(symplectic_form(&e2, &e4),  1.0);  // omega(e_2, e_4) = 1
assert_eq!(symplectic_form(&e1, &e2),  0.0);  // omega(e_1, e_2) = 0 (Lagrangian)
assert_eq!(symplectic_form(&e3, &e4),  0.0);  // omega(e_3, e_4) = 0 (Lagrangian)
```

---

### 1.5 Two-Faces and Adjacency

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

**Note:** For the Tube algorithm, 2-faces are enriched with additional data (transition matrices, trivialized polygons, rotation numbers). These fields are defined in sections 1.10-1.14 and collected in `TwoFaceEnriched`.

```rust
let two_faces: Vec<TwoFace> = {
    let mut faces = Vec::new();
    for i in 0..num_facets {
        for j in (i+1)..num_facets {
            let verts: Vec<usize> = (0..num_vertices)
                .filter(|&k|
                    (normals[i].dot(&vertices[k]) - heights[i]).abs() < EPS &&
                    (normals[j].dot(&vertices[k]) - heights[j]).abs() < EPS
                )
                .collect();
            if verts.len() >= 3 {  // 2D face needs >= 3 vertices
                let omega_ij = symplectic_form(&normals[i], &normals[j]);
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

### 1.6 Lagrangian vs Non-Lagrangian 2-Faces

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
- If some but not all 2-faces are Lagrangian, **no algorithm currently handles this case** (known limitation)

**Why trivialization fails for Lagrangian 2-faces:**

The quaternion-based trivialization τ(V) = (⟨V, Jn⟩, ⟨V, Kn⟩) requires the 2-face to project non-degenerately onto the coordinate vectors Jn, Kn.

- **Non-Lagrangian 2-faces:** Project to a 2D region → valid coordinate system
- **Lagrangian 2-faces:** When ω(n₁, n₂) = ⟨Jn₁, n₂⟩ = 0, the vector Jn₁ is perpendicular to n₂ (and already perpendicular to n₁), so Jn₁ lies in the 2-face tangent space. This means the 2-face projects to a 1D line → **degenerate**.

This degeneracy is precisely why the tube algorithm doesn't handle Lagrangian 2-faces.

---

### 1.7 Flow Direction on Non-Lagrangian 2-Faces

For a non-Lagrangian 2-face \(F_{ij}\), the Reeb flow crosses from one facet to the other. The direction depends on the sign of \(\omega(n_i, n_j)\):

- If \(\omega(n_i, n_j) > 0\): flow crosses from \(F_i\) to \(F_j\)
- If \(\omega(n_i, n_j) < 0\): flow crosses from \(F_j\) to \(F_i\)

**Proof:** See thesis `math/05-reeb-dynamics.tex:lem-nonlagrangian-2face`. The key identity is \(\langle Jn_i, n_j \rangle = \omega(n_i, n_j)\). On facet \(F_i\), the Reeb vector is \(R_i \propto Jn_i\). Its inner product with \(n_j\) determines whether \(R_i\) points into (\(<0\)) or out of (\(>0\)) the half-space \(\{x : \langle x, n_j \rangle \leq h_j\}\). When \(\omega(n_i, n_j) > 0\), we have \(\langle R_i, n_j \rangle > 0\), meaning \(R_i\) points outward from \(F_i\) toward \(F_j\).

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

### 1.8 Lagrangian Product Structure (Special Case)

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
    normals: Vec<Vector2<f64>>,    // unit outward normals, CCW order
    heights: Vec<f64>,
    vertices: Vec<Vector2<f64>>,   // CCW order, vertex[i] is intersection of edges i-1 and i
}
```

---

### 1.9 Quaternion Structure

**Source:** CH2021 §2.3 (quaternionic trivialization).

For trivializing 2-faces, we use the quaternion matrices \(\mathbf{i}, \mathbf{j}, \mathbf{k} \in \mathrm{SO}(4)\) from CH2021, where \(\mathbf{i}\) is the standard almost complex structure (symplectic J).

**Naming convention:** We use `QUAT_I`, `QUAT_J`, `QUAT_K` to match CH2021's notation and avoid confusion with the symplectic matrix J.

In coordinates \((x_1, x_2, y_1, y_2)\) (CH2021 convention):
\[
\mathbf{i} = \begin{pmatrix} 0 & 0 & -1 & 0 \\ 0 & 0 & 0 & -1 \\ 1 & 0 & 0 & 0 \\ 0 & 1 & 0 & 0 \end{pmatrix}, \quad
\mathbf{j} = \begin{pmatrix} 0 & -1 & 0 & 0 \\ 1 & 0 & 0 & 0 \\ 0 & 0 & 0 & 1 \\ 0 & 0 & -1 & 0 \end{pmatrix}, \quad
\mathbf{k} = \begin{pmatrix} 0 & 0 & 0 & -1 \\ 0 & 0 & 1 & 0 \\ 0 & -1 & 0 & 0 \\ 1 & 0 & 0 & 0 \end{pmatrix}
\]

```rust
/// QUAT_I = standard almost complex structure (symplectic J)
/// This is also J_MATRIX from §1.2
const QUAT_I: Matrix4<f64> = Matrix4::new(
    0.0,  0.0, -1.0,  0.0,
    0.0,  0.0,  0.0, -1.0,
    1.0,  0.0,  0.0,  0.0,
    0.0,  1.0,  0.0,  0.0,
);

const QUAT_J: Matrix4<f64> = Matrix4::new(
    0.0, -1.0,  0.0,  0.0,
    1.0,  0.0,  0.0,  0.0,
    0.0,  0.0,  0.0,  1.0,
    0.0,  0.0, -1.0,  0.0,
);

const QUAT_K: Matrix4<f64> = Matrix4::new(
    0.0,  0.0,  0.0, -1.0,
    0.0,  0.0,  1.0,  0.0,
    0.0, -1.0,  0.0,  0.0,
    1.0,  0.0,  0.0,  0.0,
);
```

**Quaternion relations:** \(\mathbf{i}^2 = \mathbf{j}^2 = \mathbf{k}^2 = \mathbf{ijk} = -I\), and \(\mathbf{ij} = \mathbf{k}\), \(\mathbf{jk} = \mathbf{i}\), \(\mathbf{ki} = \mathbf{j}\).

```rust
assert_eq!(QUAT_I * QUAT_I, -Matrix4::identity());  // i² = -I
assert_eq!(QUAT_J * QUAT_J, -Matrix4::identity());  // j² = -I
assert_eq!(QUAT_K * QUAT_K, -Matrix4::identity());  // k² = -I
assert_eq!(QUAT_I * QUAT_J, QUAT_K);                // ij = k
assert_eq!(QUAT_J * QUAT_K, QUAT_I);                // jk = i
assert_eq!(QUAT_K * QUAT_I, QUAT_J);                // ki = j
```

**Key properties for trivialization:**
- \(\omega_0(u, v) = \langle \mathbf{i} u, v \rangle\) (symplectic form via \(\mathbf{i}\))
- \(\omega_0(\mathbf{j}\nu, \mathbf{k}\nu) = 1\) for any unit vector \(\nu\)
- \(\{\mathbf{i}\nu, \mathbf{j}\nu, \mathbf{k}\nu\}\) is orthonormal for any unit \(\nu\)

```rust
// Symplectic form via QUAT_I
fn symplectic_form(u: &Vector4<f64>, v: &Vector4<f64>) -> f64 {
    (QUAT_I * u).dot(v)
}

// For any unit normal n:
let n = random_unit_vector();
let in_ = QUAT_I * n;
let jn = QUAT_J * n;
let kn = QUAT_K * n;

// Orthonormality
assert!(in_.dot(&jn).abs() < EPS);
assert!(in_.dot(&kn).abs() < EPS);
assert!(jn.dot(&kn).abs() < EPS);

// Symplectic property: ω(jn, kn) = 1
assert!((symplectic_form(&jn, &kn) - 1.0).abs() < EPS);
```

---

### 1.10 Trivialization of 2-Face Tangent Spaces

**Source:** CH2021 Definition 2.15 (quaternionic trivialization), Lemma 2.16 (symplectic preservation).

Each non-Lagrangian 2-face \(F_{ij}\) has a 2-dimensional tangent space. We trivialize it using the quaternion structure.

**Setup:** For a 2-face \(F_{ij} = F_i \cap F_j\), the tangent space is:
\[
T_p F_{ij} = \{ V \in \mathbb{R}^4 : \langle V, n_i \rangle = 0 \text{ and } \langle V, n_j \rangle = 0 \}
\]
This is 2-dimensional (intersection of two hyperplanes in 4D).

**Definition:** The trivialization \(\tau_n: T_p F \to \mathbb{R}^2\) with respect to unit normal \(n\) (CH2021 Definition 2.15):
\[
\tau_n(V) = (\langle V, \mathbf{j}n \rangle, \langle V, \mathbf{k}n \rangle)
\]
where \(\mathbf{j}, \mathbf{k}\) are the quaternion matrices (see §1.9).

```rust
fn trivialize(n: &Vector4<f64>, v: &Vector4<f64>) -> Vector2<f64> {
    let jn = QUAT_J * n;
    let kn = QUAT_K * n;
    Vector2::new(v.dot(&jn), v.dot(&kn))
}
```

**CRITICAL:** This function maps 4D vectors to 2D coordinates. It is an **isomorphism** when restricted to a 2-face tangent space TF, but it does NOT have a simple inverse formula. See below.

**Why trivialize works on 2-faces (CH2021 Lemma 2.16):**
- For a 2-face F at intersection of facets with normals \(n_i\) (entry) and \(n_j\) (exit)
- TF ⊂ T(F_exit), since the 2-face lies on the exit facet
- \(\{\mathbf{i}n_j, \mathbf{j}n_j, \mathbf{k}n_j\}\) is an orthonormal basis for T(F_exit)
- Any \(V \in TF\) can be written in this basis; \(\tau_{n_j}(V)\) extracts the \(\mathbf{j}, \mathbf{k}\) components

**WRONG inverse (from old spec, DO NOT USE):**
```rust
// WRONG: This gives a vector in span{jn, kn}, NOT in TF
// fn untrivialize_WRONG(n: &Vector4<f64>, coords: &Vector2<f64>) -> Vector4<f64> {
//     QUAT_J * n * coords[0] + QUAT_K * n * coords[1]
// }
```

**CORRECT inverse requires explicit basis vectors in TF.** See §1.10.1 below.

**Assertions:**
```rust
let jn = QUAT_J * n;
let kn = QUAT_K * n;

// jn and kn are orthonormal
assert!(jn.dot(&kn).abs() < EPS);  // orthogonal
assert!((jn.norm() - 1.0).abs() < EPS);  // unit length
assert!((kn.norm() - 1.0).abs() < EPS);  // unit length

// jn and kn are tangent to the facet (perpendicular to n)
assert!(jn.dot(n).abs() < EPS);
assert!(kn.dot(n).abs() < EPS);

// Symplectic: ω(jn, kn) = 1
assert!((symplectic_form(&jn, &kn) - 1.0).abs() < EPS);
```

**Key property (symplectic form preservation):** (CH2021 Lemma 2.16)

For vectors \(V_1, V_2\) **in the 2-face tangent space TF**:
\[
\omega(V_1, V_2) = \omega_{\text{std}}(\tau_n(V_1), \tau_n(V_2))
\]
where \(\omega_{\text{std}}(x, y) = x_1 y_2 - x_2 y_1\) is the standard 2D symplectic form.

```rust
fn symplectic_form_2d(x: &Vector2<f64>, y: &Vector2<f64>) -> f64 {
    x[0] * y[1] - x[1] * y[0]
}
```

---

### 1.10.1 Explicit Basis Vectors for 2-Face Reconstruction

**Source:** Derived from CH2021 Definition 2.15. See `trivialization-derivation.md` for full derivation.

To reconstruct 4D points from 2D coordinates, we need **explicit basis vectors** that lie IN the 2-face tangent space TF.

**Setup:** For a 2-face F at intersection of facets with normals \(n_{\text{entry}}\) and \(n_{\text{exit}}\):
\[
TF = \{ V \in \mathbb{R}^4 : \langle V, n_{\text{entry}} \rangle = 0 \text{ and } \langle V, n_{\text{exit}} \rangle = 0 \}
\]

**Exit basis:** Find \(b_1^{\text{exit}}, b_2^{\text{exit}} \in TF\) such that:
- \(\tau_{n_{\text{exit}}}(b_1^{\text{exit}}) = (1, 0)\)
- \(\tau_{n_{\text{exit}}}(b_2^{\text{exit}}) = (0, 1)\)

This means:
- \(\langle b_1^{\text{exit}}, \mathbf{j} n_{\text{exit}} \rangle = 1\), \(\langle b_1^{\text{exit}}, \mathbf{k} n_{\text{exit}} \rangle = 0\)
- \(\langle b_2^{\text{exit}}, \mathbf{j} n_{\text{exit}} \rangle = 0\), \(\langle b_2^{\text{exit}}, \mathbf{k} n_{\text{exit}} \rangle = 1\)

**Matrix formulation:** Define \(M_{\text{exit}}\) with rows \([n_{\text{entry}}, n_{\text{exit}}, \mathbf{j} n_{\text{exit}}, \mathbf{k} n_{\text{exit}}]\):
\[
b_1^{\text{exit}} = M_{\text{exit}}^{-1} \cdot [0, 0, 1, 0]^T \quad \text{(3rd column of } M_{\text{exit}}^{-1}\text{)}
\]
\[
b_2^{\text{exit}} = M_{\text{exit}}^{-1} \cdot [0, 0, 0, 1]^T \quad \text{(4th column of } M_{\text{exit}}^{-1}\text{)}
\]

```rust
fn compute_exit_basis(n_entry: &Vector4<f64>, n_exit: &Vector4<f64>) -> [Vector4<f64>; 2] {
    let jn_exit = QUAT_J * n_exit;
    let kn_exit = QUAT_K * n_exit;

    // Build matrix M with rows: n_entry, n_exit, jn_exit, kn_exit
    let m = Matrix4::from_rows(&[
        n_entry.transpose(),
        n_exit.transpose(),
        jn_exit.transpose(),
        kn_exit.transpose(),
    ]);

    let m_inv = m.try_inverse().expect("Degenerate 2-face: M not invertible");

    // Extract 3rd and 4th columns
    [m_inv.column(2).into(), m_inv.column(3).into()]
}
```

**Entry basis:** Similarly, using \(n_{\text{entry}}\) for trivialization:
```rust
fn compute_entry_basis(n_entry: &Vector4<f64>, n_exit: &Vector4<f64>) -> [Vector4<f64>; 2] {
    let jn_entry = QUAT_J * n_entry;
    let kn_entry = QUAT_K * n_entry;

    let m = Matrix4::from_rows(&[
        n_entry.transpose(),
        n_exit.transpose(),
        jn_entry.transpose(),
        kn_entry.transpose(),
    ]);

    let m_inv = m.try_inverse().expect("Degenerate 2-face: M not invertible");
    [m_inv.column(2).into(), m_inv.column(3).into()]
}
```

**Reconstruction (the correct "untrivialize"):**
```rust
fn untrivialize_with_basis(
    coords: &Vector2<f64>,
    basis: &[Vector4<f64>; 2],
    centroid: &Vector4<f64>,
) -> Vector4<f64> {
    centroid + coords[0] * basis[0] + coords[1] * basis[1]
}
```

**Assertions:**
```rust
// Basis vectors lie in TF (perpendicular to BOTH normals)
assert!(b_exit[0].dot(&n_entry).abs() < EPS);
assert!(b_exit[0].dot(&n_exit).abs() < EPS);
assert!(b_exit[1].dot(&n_entry).abs() < EPS);
assert!(b_exit[1].dot(&n_exit).abs() < EPS);

// Basis gives correct coordinates under trivialization
let jn_exit = QUAT_J * n_exit;
let kn_exit = QUAT_K * n_exit;
assert!((b_exit[0].dot(&jn_exit) - 1.0).abs() < EPS);
assert!(b_exit[0].dot(&kn_exit).abs() < EPS);
assert!(b_exit[1].dot(&jn_exit).abs() < EPS);
assert!((b_exit[1].dot(&kn_exit) - 1.0).abs() < EPS);

// Round-trip works for vectors in TF
let v = 0.3 * b_exit[0] + 0.7 * b_exit[1];  // A vector in TF
let coords = trivialize(&n_exit, &v);
let v_recovered = coords[0] * b_exit[0] + coords[1] * b_exit[1];
assert!((v_recovered - v).norm() < EPS);
```

---

### 1.11 Transition Matrices on 2-Faces

**Source:** CH2021 Definition 2.17 (transition matrix), Lemma 2.18 (positive elliptic classification).

For a non-Lagrangian 2-face \(F\) at intersection of facets with normals \(n_{\text{entry}}\) and \(n_{\text{exit}}\), the **transition matrix** \(\psi_F \in \mathrm{Sp}(2)\) converts entry-trivialization coordinates to exit-trivialization coordinates:
\[
\psi_F = \tau_{n_{\text{exit}}} \circ \tau_{n_{\text{entry}}}^{-1}
\]

**Two equivalent computation methods:**

**Method A: Using explicit basis vectors (recommended)**

Since \(\tau_{n_{\text{entry}}}^{-1}(1,0) = b_1^{\text{entry}}\) and \(\tau_{n_{\text{entry}}}^{-1}(0,1) = b_2^{\text{entry}}\):

```rust
fn compute_transition_matrix_basis(
    b_entry: &[Vector4<f64>; 2],
    n_exit: &Vector4<f64>,
) -> Matrix2<f64> {
    let jn_exit = QUAT_J * n_exit;
    let kn_exit = QUAT_K * n_exit;

    // Column k of ψ is τ_{n_exit}(b_k^entry)
    Matrix2::new(
        b_entry[0].dot(&jn_exit), b_entry[1].dot(&jn_exit),
        b_entry[0].dot(&kn_exit), b_entry[1].dot(&kn_exit),
    )
}
```

**Method B: CH2021 direct formula (for verification)**

From CH2021 Lemma 2.17, using:
\[
a_1 = \langle n_{\text{entry}}, n_{\text{exit}} \rangle, \quad
a_2 = \langle \mathbf{i} n_{\text{entry}}, n_{\text{exit}} \rangle, \quad
a_3 = \langle \mathbf{j} n_{\text{entry}}, n_{\text{exit}} \rangle, \quad
a_4 = \langle \mathbf{k} n_{\text{entry}}, n_{\text{exit}} \rangle
\]

\[
\psi_F = \frac{1}{a_2} \begin{pmatrix} a_1 a_2 - a_3 a_4 & -(a_2^2 + a_4^2) \\ a_2^2 + a_3^2 & a_1 a_2 + a_3 a_4 \end{pmatrix}
\]

```rust
fn compute_transition_matrix_ch2021(
    n_entry: &Vector4<f64>,
    n_exit: &Vector4<f64>,
) -> Matrix2<f64> {
    let a1 = n_entry.dot(n_exit);
    let a2 = (QUAT_I * n_entry).dot(n_exit);
    let a3 = (QUAT_J * n_entry).dot(n_exit);
    let a4 = (QUAT_K * n_entry).dot(n_exit);

    debug_assert!(a2.abs() > EPS, "a2 ≈ 0 indicates Lagrangian 2-face or wrong flow direction");

    let inv_a2 = 1.0 / a2;
    Matrix2::new(
        inv_a2 * (a1 * a2 - a3 * a4), inv_a2 * -(a2 * a2 + a4 * a4),
        inv_a2 * (a2 * a2 + a3 * a3), inv_a2 * (a1 * a2 + a3 * a4),
    )
}
```

**Cross-validation:** Both methods should give the same result:
```rust
let psi_basis = compute_transition_matrix_basis(&b_entry, &n_exit);
let psi_ch2021 = compute_transition_matrix_ch2021(&n_entry, &n_exit);
assert!((psi_basis - psi_ch2021).norm() < EPS, "Methods disagree!");
```

**Assertions:**
```rust
// ψ is symplectic: det(ψ) = 1
assert!((psi.determinant() - 1.0).abs() < EPS);

// Trace formula: tr(ψ) = 2⟨n_entry, n_exit⟩
let expected_trace = 2.0 * n_entry.dot(&n_exit);
assert!((psi.trace() - expected_trace).abs() < EPS);
```

**Classification by trace** (CH2021 Lemma 2.18; see also Appendix A, Definition A.3):
- \(|\mathrm{tr}(\psi)| > 2\): Hyperbolic (cannot occur for polytope 2-faces — the transition matrix is always positive elliptic)
- \(|\mathrm{tr}(\psi)| = 2\): Parabolic = Lagrangian 2-face (ω(n_i, n_j) = 0)
- \(|\mathrm{tr}(\psi)| < 2\): Elliptic = non-Lagrangian 2-face

```rust
// For non-Lagrangian 2-faces only: ψ is positive elliptic (|tr| < 2)
// This condition is EQUIVALENT to ω(n_i, n_j) ≠ 0
fn assert_non_lagrangian(psi: &Matrix2<f64>, n_i: &Vector4<f64>, n_j: &Vector4<f64>) {
    let trace = psi.trace();
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

### 1.12 Rotation Number of 2-Faces

**Source:** CH2021 Appendix A (rotation numbers on Sp(2)), Lemma 2.17 (positive elliptic), Corollary 5.3.

For a non-Lagrangian 2-face \(F\), the **rotation number** \(\rho(F) \in (0, 0.5)\) measures how much the Reeb flow "rotates" when crossing.

**Formula:**
\[
\rho(F) = \frac{1}{2\pi} \arccos\left(\frac{1}{2} \mathrm{tr}(\psi_F)\right)
\]

**Why \(|\mathrm{tr}(\psi)| < 2\) is guaranteed (CH2021 Lemma 2.17):**

From the trace formula in §1.11:
\[
\mathrm{tr}(\psi_F) = 2 \langle n_{\text{entry}}, n_{\text{exit}} \rangle
\]

Since \(n_{\text{entry}}\) and \(n_{\text{exit}}\) are distinct unit normals of adjacent facets:
- They cannot be equal (distinct facets): \(\langle n_{\text{entry}}, n_{\text{exit}} \rangle \neq 1\)
- They cannot be opposite (convexity prevents this for adjacent facets): \(\langle n_{\text{entry}}, n_{\text{exit}} \rangle \neq -1\)
- Therefore: \(|\mathrm{tr}(\psi_F)| < 2\) always holds

This means \(\psi_F\) is **always elliptic** for non-Lagrangian 2-faces. Clamping is only for floating point robustness:

```rust
impl TwoFaceEnriched {
    fn rotation_number(&self) -> f64 {
        let trace = self.transition_matrix.trace();

        // Sanity check: tr = 2⟨n_entry, n_exit⟩, which is in (-2, 2) for valid 2-faces
        debug_assert!(trace.abs() < 2.0 + EPS,
            "Transition matrix not elliptic: tr = {}", trace);

        // Clamp only for floating point robustness
        let half_trace = (0.5 * trace).clamp(-1.0 + EPS, 1.0 - EPS);
        half_trace.acos() / (2.0 * std::f64::consts::PI)
    }
}
```

**Simpler direct formula:** Since tr(ψ) = 2⟨n_entry, n_exit⟩:
\[
\rho(F) = \frac{1}{2\pi} \arccos\left(\langle n_{\text{entry}}, n_{\text{exit}} \rangle\right)
\]

The rotation is just the **angle between the normals** divided by 2π:

```rust
fn rotation_number_direct(n_entry: &Vector4<f64>, n_exit: &Vector4<f64>) -> f64 {
    let cos_angle = n_entry.dot(n_exit).clamp(-1.0 + EPS, 1.0 - EPS);
    cos_angle.acos() / (2.0 * std::f64::consts::PI)
}
```

**Classification by trace:**
- \(|\mathrm{tr}| > 2\): Hyperbolic — **cannot occur** for polytope 2-faces
- \(|\mathrm{tr}| = 2\): Parabolic — impossible (requires parallel normals)
- \(|\mathrm{tr}| < 2\): Elliptic — always, with \(\rho \in (0, 0.5)\)

**Why rotation is flow-direction-independent:** tr(ψ) = tr(ψ⁻¹) for symplectic matrices, so the rotation number is the same for both flow directions.

**Significance for Tube algorithm (CH2021 Prop 1.8):**
- Every Reeb orbit has total rotation \(\rho > 1\) turn
- Action-minimizing orbits have \(\rho \leq 2\) turns
- The algorithm prunes paths where accumulated rotation exceeds 2 turns

---

### 1.13 Support Function and Polar Body

The **support function** of \(K\):
\[
h_K(d) = \max_{x \in K} \langle d, x \rangle
\]

For H-rep polytope, this is computable via the vertices:
```rust
fn support_function(vertices: &[Vector4<f64>], direction: &Vector4<f64>) -> f64 {
    vertices.iter()
        .map(|v| direction.dot(v))
        .fold(f64::NEG_INFINITY, f64::max)
}
```

The **polar body** (dual) of \(K\):
\[
K^\circ = \{ y \in \mathbb{R}^4 : \langle x, y \rangle \leq 1 \text{ for all } x \in K \}
\]

For a 2D polygon in H-rep \(\{x : \langle n_i, x \rangle \leq h_i\}\), the polar has vertices at \(n_i / h_i\):

```rust
fn polar_vertices_2d(normals: &[Vector2<f64>], heights: &[f64]) -> Vec<Vector2<f64>> {
    normals.iter().zip(heights)
        .map(|(n, &h)| n / h)
        .collect()
}
```

**Significance for Billiard algorithm:** The "T-length" of a billiard trajectory is measured using \(K_2^\circ\) as the unit ball, i.e., via \(h_{K_2}(\cdot)\).

---

### 1.14 Trivialized 2-Face Polygons

For the Tube algorithm, we need each 2-face as a 2D polygon in trivialized coordinates.

```rust
// See below for the full TwoFaceEnriched struct definition

fn enrich_two_face(
    two_face: &TwoFace,
    vertices: &[Vector4<f64>],
    n_i: &Vector4<f64>,  // normal of facet i
    n_j: &Vector4<f64>,  // normal of facet j
) -> TwoFaceEnriched {
    // Determine flow direction and set flow-aware normals
    let (entry_normal, exit_normal) = match two_face.flow_direction() {
        Some(FlowDirection::ItoJ) => (n_i.clone(), n_j.clone()),
        Some(FlowDirection::JtoI) => (n_j.clone(), n_i.clone()),
        None => panic!("Cannot enrich Lagrangian 2-face for Tube algorithm"),
    };

    // Compute flow-aware transition matrix: entry→exit
    let transition_matrix = compute_transition_matrix(&entry_normal, &exit_normal);

    // Compute rotation number (unsigned, does not depend on flow direction)
    let rotation = compute_rotation_number(&transition_matrix);

    // Trivialize vertices using EXIT normal (CH2021 convention)
    let verts_4d: Vec<Vector4<f64>> = two_face.vertices.iter()
        .map(|&i| vertices[i])
        .collect();
    let centroid: Vector4<f64> = verts_4d.iter().sum::<Vector4<f64>>() / verts_4d.len() as f64;
    let polygon_2d: Vec<Vector2<f64>> = verts_4d.iter()
        .map(|v| trivialize(&exit_normal, &(v - centroid)))
        .collect();
    let polygon_2d = sort_ccw(polygon_2d);

    TwoFaceEnriched {
        i: two_face.i,
        j: two_face.j,
        vertices: two_face.vertices.clone(),
        omega_ij: two_face.omega_ij,
        is_lagrangian: two_face.is_lagrangian(),
        flow_direction: two_face.flow_direction(),
        transition_matrix,
        rotation,
        entry_normal,
        exit_normal,
        polygon_2d,
        vertices_4d: verts_4d,
        centroid_4d: centroid,
    }
}
```

**Consolidated TwoFaceEnriched (all fields from sections 1.5-1.7, 1.11-1.14):**

**IMPORTANT: Trivialization Normal Convention (CH2021)**

Per CH2021 Definition 2.15: "Let ν denote the **outward unit normal vector to E**" where E is the facet the Reeb flow **points into** (the exit facet).

**Flow-direction-aware fields:** The `entry_normal`, `exit_normal`, and `transition_matrix` fields are computed based on actual flow direction, NOT the canonical i < j ordering:

| Flow direction | entry_normal | exit_normal | transition_matrix |
|----------------|--------------|-------------|-------------------|
| ItoJ (ω > 0) | n_i | n_j | τ_{n_j} ∘ τ_{n_i}^{-1} |
| JtoI (ω < 0) | n_j | n_i | τ_{n_i} ∘ τ_{n_j}^{-1} |

This design means callers can use `entry_normal`, `exit_normal`, and `transition_matrix` directly without checking `flow_direction`.

**Design rationale:** We considered two approaches:
- **(A) Canonical fields:** Always store n_i, n_j, ψ_{i→j} regardless of flow direction. Callers check `flow_direction` and invert as needed.
- **(B) Flow-aware fields:** Store actual entry/exit normals and the correct entry→exit transition matrix based on flow direction.

We chose **(B)** because the Tube algorithm code becomes simpler and less error-prone — the extend_tube function can apply `transition_matrix` directly without flow-direction checks. The cost is more work in `enrich_two_face`, but that's computed once per 2-face.

```rust
struct TwoFaceEnriched {
    // From 1.5: Basic identification
    i: usize,                          // first facet index (i < j by convention)
    j: usize,                          // second facet index
    vertices: Vec<usize>,              // indices into global vertex list
    omega_ij: f64,                     // ω(n_i, n_j)

    // From 1.6: Lagrangian classification
    is_lagrangian: bool,               // |omega_ij| < EPS_LAGRANGIAN

    // From 1.7: Flow direction (for non-Lagrangian)
    flow_direction: Option<FlowDirection>,  // ItoJ or JtoI

    // From 1.11: Transition matrix (for non-Lagrangian)
    // FLOW-AWARE: This is τ_{exit} ∘ τ_{entry}^{-1}, the entry→exit coordinate map.
    // For ItoJ: τ_{n_j} ∘ τ_{n_i}^{-1}. For JtoI: τ_{n_i} ∘ τ_{n_j}^{-1}.
    transition_matrix: Matrix2<f64>,   // entry→exit map ∈ Sp(2)

    // From 1.12: Rotation number (for non-Lagrangian)
    rotation: f64,                     // ρ(F) ∈ (0, 0.5), unsigned

    // From 1.14: Trivialized polygon (FLOW-AWARE)
    // CONVENTION (CH2021): polygon_2d uses exit_normal for trivialization.
    // entry_normal and exit_normal are set based on flow_direction (see table above).
    entry_normal: Vector4<f64>,        // normal of facet we entered from
    exit_normal: Vector4<f64>,         // normal of facet we exit to (PRIMARY, per CH2021)
    polygon_2d: Vec<Vector2<f64>>,     // vertices in τ_{exit_normal} coordinates, CCW
    vertices_4d: Vec<Vector4<f64>>,    // original 4D vertex positions
    centroid_4d: Vector4<f64>,         // centroid for reconstruction
}
```

---

### 1.15 Edge and Vertex Incidence

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

### 1.16 Constants and Tolerances

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

### 1.17 Helper Functions (Geometry Utilities)

**CCW sorting of 2D polygon vertices:**

```rust
/// Sort 2D points in counter-clockwise order around their centroid.
/// Precondition: points form a convex polygon (no collinearity checks).
fn sort_ccw(mut points: Vec<Vector2<f64>>) -> Vec<Vector2<f64>> {
    if points.len() < 3 {
        return points;
    }

    // Compute centroid
    let centroid: Vector2<f64> = points.iter().sum::<Vector2<f64>>() / points.len() as f64;

    // Sort by angle from centroid
    points.sort_by(|a, b| {
        let angle_a = (a[1] - centroid[1]).atan2(a[0] - centroid[0]);
        let angle_b = (b[1] - centroid[1]).atan2(b[0] - centroid[0]);
        angle_a.partial_cmp(&angle_b).unwrap()
    });

    points
}
```

**Convex polygon intersection (Sutherland-Hodgman-style):**

```rust
/// Compute intersection of two convex polygons.
/// Returns empty polygon if intersection is empty.
/// Reference: O'Rourke, "Computational Geometry in C", Chapter 7.
fn intersect_polygons(p1: &Polygon2D, p2: &Polygon2D) -> Polygon2D {
    // Clip p1 against each edge of p2
    let mut result = p1.vertices.clone();

    for i in 0..p2.vertices.len() {
        if result.is_empty() {
            break;
        }
        let j = (i + 1) % p2.vertices.len();
        let edge_start = &p2.vertices[i];
        let edge_end = &p2.vertices[j];

        result = clip_polygon_by_halfplane(&result, edge_start, edge_end);
    }

    Polygon2D { vertices: result }
}

/// Clip polygon by half-plane defined by edge (p1 -> p2).
/// Keep points on the left side of the directed edge.
fn clip_polygon_by_halfplane(
    polygon: &[Vector2<f64>],
    p1: &Vector2<f64>,
    p2: &Vector2<f64>,
) -> Vec<Vector2<f64>> {
    let mut output = Vec::new();

    for i in 0..polygon.len() {
        let j = (i + 1) % polygon.len();
        let curr = &polygon[i];
        let next = &polygon[j];

        let curr_inside = is_left_of_edge(curr, p1, p2);
        let next_inside = is_left_of_edge(next, p1, p2);

        if curr_inside {
            output.push(*curr);
            if !next_inside {
                output.push(line_intersection(curr, next, p1, p2));
            }
        } else if next_inside {
            output.push(line_intersection(curr, next, p1, p2));
        }
    }

    output
}

fn is_left_of_edge(p: &Vector2<f64>, e1: &Vector2<f64>, e2: &Vector2<f64>) -> bool {
    // Cross product of (e2-e1) and (p-e1)
    let cross = (e2[0] - e1[0]) * (p[1] - e1[1]) - (e2[1] - e1[1]) * (p[0] - e1[0]);
    cross >= -EPS  // Include points on the edge
}

fn line_intersection(
    a1: &Vector2<f64>, a2: &Vector2<f64>,
    b1: &Vector2<f64>, b2: &Vector2<f64>,
) -> Vector2<f64> {
    // Standard line-line intersection formula
    let d1 = a2 - a1;
    let d2 = b2 - b1;
    let cross = d1[0] * d2[1] - d1[1] * d2[0];

    if cross.abs() < EPS {
        // Lines are parallel; return midpoint as fallback
        return (a1 + b1) / 2.0;
    }

    let t = ((b1[0] - a1[0]) * d2[1] - (b1[1] - a1[1]) * d2[0]) / cross;
    a1 + d1 * t
}
```

**Point-in-polygon test:**

```rust
/// Test if point is inside a convex polygon (CCW vertices).
/// Uses winding number method.
fn point_in_polygon(p: &Vector2<f64>, polygon: &Polygon2D) -> bool {
    if polygon.vertices.len() < 3 {
        return false;
    }

    // For convex polygons: point is inside iff it's on the left of all edges
    for i in 0..polygon.vertices.len() {
        let j = (i + 1) % polygon.vertices.len();
        if !is_left_of_edge(p, &polygon.vertices[i], &polygon.vertices[j]) {
            return false;
        }
    }
    true
}
```

**Affine map composition:**

```rust
impl AffineMap2D {
    fn identity() -> Self {
        AffineMap2D {
            matrix: Matrix2::identity(),
            offset: Vector2::zeros(),
        }
    }

    fn apply(&self, x: &Vector2<f64>) -> Vector2<f64> {
        self.matrix * x + self.offset
    }
}

/// Compose f ∘ g: (Ax + b) ∘ (Cx + d) = A(Cx + d) + b = (AC)x + (Ad + b)
fn compose_affine(f: &AffineMap2D, g: &AffineMap2D) -> AffineMap2D {
    AffineMap2D {
        matrix: f.matrix * g.matrix,
        offset: f.matrix * g.offset + f.offset,
    }
}

fn apply_affine_map(f: &AffineMap2D, polygon: &Polygon2D) -> Polygon2D {
    Polygon2D {
        vertices: polygon.vertices.iter().map(|v| f.apply(v)).collect(),
    }
}
```

**Affine function operations:**

```rust
impl AffineFunc {
    fn zero() -> Self {
        AffineFunc {
            gradient: Vector2::zeros(),
            constant: 0.0,
        }
    }

    fn eval(&self, x: &Vector2<f64>) -> f64 {
        self.gradient.dot(x) + self.constant
    }
}

/// Add two affine functions: (g₁·x + c₁) + (g₂·x + c₂) = (g₁+g₂)·x + (c₁+c₂)
fn add_affine_funcs(f: &AffineFunc, g: &AffineFunc) -> AffineFunc {
    AffineFunc {
        gradient: f.gradient + g.gradient,
        constant: f.constant + g.constant,
    }
}

/// Compose affine function with affine map: f(Ax + b) where f(y) = g·y + c
/// Result: g·(Ax + b) + c = (Aᵀg)·x + (g·b + c)
fn compose_with_map(f: &AffineFunc, map: &AffineMap2D) -> AffineFunc {
    AffineFunc {
        gradient: map.matrix.transpose() * f.gradient,
        constant: f.gradient.dot(&map.offset) + f.constant,
    }
}
```

**Polygon area (for emptiness check):**

```rust
fn polygon_area(p: &Polygon2D) -> f64 {
    if p.vertices.len() < 3 {
        return 0.0;
    }

    let mut area = 0.0;
    for i in 0..p.vertices.len() {
        let j = (i + 1) % p.vertices.len();
        area += p.vertices[i][0] * p.vertices[j][1];
        area -= p.vertices[j][0] * p.vertices[i][1];
    }
    (area / 2.0).abs()
}
```

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
    vertices: Vec<Vector4<f64>>,  // vertices[0], ..., vertices[n-1]
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
fn action_of_closed_polygon(vertices: &[Vector4<f64>]) -> f64 {
    let n = vertices.len();
    let mut sum = 0.0;
    for k in 0..n {
        sum += symplectic_form(&vertices[k], &vertices[(k + 1) % n]);
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
fn is_on_boundary(p: &Vector4<f64>, hrep: &PolytopeHRep) -> bool {
    let on_some_facet = hrep.normals.iter().zip(&hrep.heights)
        .any(|(n, &h)| (n.dot(p) - h).abs() < EPS);
    let inside_all = hrep.normals.iter().zip(&hrep.heights)
        .all(|(n, &h)| n.dot(p) <= h + EPS);
    on_some_facet && inside_all
}

fn active_facets(p: &Vector4<f64>, hrep: &PolytopeHRep) -> Vec<usize> {
    hrep.normals.iter().zip(&hrep.heights).enumerate()
        .filter(|(_, (n, &h))| (n.dot(p) - h).abs() < EPS)
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
assert!(reeb_vectors[i].dot(&normals[i]).abs() < EPS);

// Reeb vector magnitude = 2/h_i
assert!((reeb_vectors[i].norm() - 2.0 / heights[i]).abs() < EPS);
```

**Cone membership:** At a point on multiple facets, the velocity is a non-negative combination:
\[
\dot\gamma(t) = \sum_{i \in \text{active}(\gamma(t))} \lambda_i R_i, \quad \lambda_i \geq 0
\]

```rust
fn is_valid_reeb_velocity(
    velocity: &Vector4<f64>,
    active_facets: &[usize],
    reeb_vectors: &[Vector4<f64>],
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
    breakpoints: Vec<Vector4<f64>>,   // p_0, p_1, ..., p_m
    segment_facets: Vec<usize>,       // which facet's Reeb vector for each segment
    segment_times: Vec<f64>,          // duration of each segment
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
    p_start: &Vector4<f64>,
    p_end: &Vector4<f64>,
    facet_idx: usize,
    heights: &[f64],
) -> f64 {
    let displacement = (p_end - p_start).norm();
    heights[facet_idx] * displacement / 2.0
}
```

**Assertions:**
```rust
// Velocity matches Reeb vector
let velocity = (breakpoints[k+1] - breakpoints[k]) / segment_times[k];
let expected_velocity = &reeb_vectors[segment_facets[k]];
assert!((velocity - expected_velocity).norm() < EPS);

// Both endpoints on claimed facet
assert!((normals[i].dot(&breakpoints[k]) - heights[i]).abs() < EPS);
assert!((normals[i].dot(&breakpoints[k+1]) - heights[i]).abs() < EPS);
```

---

### 2.5 Action of Piecewise Linear Reeb Trajectories

**Source:** Thesis Section 6 (action-capacity-systolic), Hofer-Zehnder 1994 §3.4.

For Reeb dynamics, **action equals period**:
\[
A(\gamma) = T = \sum_k \tau_k
\]

**Proof sketch:** The Reeb vector \(R\) is defined by \(\alpha(R) = 1\) and \(\iota_R d\alpha = 0\). For a Reeb orbit \(\gamma\) parametrized by \(t \in [0, T]\):
\[
A(\gamma) = \int_\gamma \alpha = \int_0^T \alpha(\dot{\gamma}(t))\, dt = \int_0^T \alpha(R)\, dt = \int_0^T 1\, dt = T
\]
On polytopes, this holds piecewise on each facet since the Reeb vector is constant within each facet.

```rust
fn action_from_segment_times(segment_times: &[f64]) -> f64 {
    segment_times.iter().sum()
}

fn action_from_breakpoints_and_facets(
    breakpoints: &[Vector4<f64>],
    segment_facets: &[usize],
    heights: &[f64],
) -> f64 {
    let mut total = 0.0;
    for k in 0..segment_facets.len() {
        let disp = (breakpoints[k + 1] - breakpoints[k]).norm();
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
    period: f64,                      // T = action
    breakpoints: Vec<Vector4<f64>>,   // p_0, ..., p_m with p_m = p_0
    segment_facets: Vec<usize>,       // i_0, ..., i_{m-1}
    segment_times: Vec<f64>,          // τ_0, ..., τ_{m-1}
}
```

**Mathematical conditions (beyond trajectory conditions):**
1. Closure: `breakpoints[m] == breakpoints[0]`
2. `breakpoints.len() == segment_facets.len() + 1`
3. `period == Σ segment_times`

**Assertions:**
```rust
// Closure
assert!((breakpoints[breakpoints.len()-1] - breakpoints[0]).norm() < EPS);

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
    breakpoints: Vec<Vector4<f64>>,
    segment_facets: Vec<usize>,
    segment_times: Vec<f64>,
}
```

**Mathematical conditions (beyond closed orbit conditions):**
- Simplicity: all elements of `segment_facets` are distinct

**Assertions:**
```rust
use std::collections::HashSet;

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

**Terminology for tube closure:**

- **Initial tube:** A tube with facet_sequence = \([i_0, i_1]\) (length 2). Represents zero-length trajectories at a single 2-face.
- **Closed tube:** A non-initial tube where start 2-face = end 2-face. For sequence \([i_0, i_1, \ldots, i_m]\), this means \(i_{m-1} = i_0\) AND \(i_m = i_1\).
- **Next-step closeable tube:** A tube where first facet = last facet (\(i_0 = i_{m-1}\)). Extending with \(i_1\) yields a closed tube (if geometrically valid).

**Lemma (minimum closed tube length is 5):**

A closed tube requires at least 3 distinct facets, giving minimum sequence length 5.

*Proof:* Consider whether length 4 is possible with sequence \([i, j, i, j]\):
- This would require: flow from facet \(i\) to \(j\) at 2-face \(F_{i,j}\), then flow from \(j\) back to \(i\) at 2-face \(F_{j,i}\).
- But \(F_{i,j} = F_{j,i}\) (same 2-face, unordered).
- Flow direction at a 2-face is fixed by \(\omega(n_i, n_j)\): if \(\omega(n_i, n_j) > 0\), flow always goes \(i \to j\).
- By antisymmetry, \(\omega(n_j, n_i) = -\omega(n_i, n_j) < 0\), so flow cannot go \(j \to i\) at this 2-face.
- Therefore length 4 is impossible for non-Lagrangian 2-faces.

Minimum is length 5 with 3 distinct facets: \([i_0, i_1, i_2, i_0, i_1]\). \(\blacksquare\)

*Example:* For facets A, B, C with compatible flow directions:
- Start at 2-face (A, B), flow A → B
- Cross to 2-face (B, C), flow B → C
- Cross to 2-face (C, A), flow C → A
- Return to 2-face (A, B), completing the closed orbit

**Lemma:** Every closed tube is the one-step extension of a unique next-step closeable tube. Proof: Remove the last element \(i_1\) from the closed tube's sequence. \(\blacksquare\)

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

    fn is_initial(&self) -> bool {
        self.facets.len() == 2
    }

    fn is_next_step_closeable(&self) -> bool {
        // A tube is next-step closeable if first facet = last facet.
        // Extending with facets[1] then yields a closed tube (if geometrically valid).
        self.facets.len() >= 3 && self.facets[0] == self.facets[self.facets.len() - 1]
    }

    fn is_closed(&self) -> bool {
        // A tube is closed if start 2-face = end 2-face and it's not initial.
        // Start 2-face: F_{facets[0], facets[1]}
        // End 2-face: F_{facets[m-1], facets[m]} where m = len - 1
        // Equality requires: facets[m-1] = facets[0] AND facets[m] = facets[1]
        if self.facets.len() < 4 {
            return false;  // Initial (len 2) or too short (len 3 impossible)
        }
        let m = self.facets.len() - 1;
        self.facets[m - 1] == self.facets[0] && self.facets[m] == self.facets[1]
    }
}
```

---

### 2.9 Tubes (Partial Trajectories)

**Source:** This thesis (Stöhler 2026). The mathematical foundations (linear flows, flow composition) come from CH2021 Definitions 2.5-2.8, but the "tube" terminology and data structure are original to this thesis. The name comes from visualizing the set of all trajectories with a fixed facet sequence as a 2-parameter family (like a tube in phase space).

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
    matrix: Matrix2<f64>,   // A
    offset: Vector2<f64>,   // b
    // Apply: f(x) = Ax + b
}

struct AffineFunc {
    gradient: Vector2<f64>, // g
    constant: f64,          // c
    // Evaluate: f(x) = ⟨g, x⟩ + c
}
```

**Rotation convention:**
- **rot(init) = 0:** A root tube (facet_sequence = [i, j]) has rotation = 0.
- **Non-decreasing:** Rotation increments are always ≥ 0 as the tube extends. Each 2-face crossing adds its rotation number ρ(F) ∈ (0, 0.5).
- **Pruning bound:** Total rotation for a minimum-action orbit is in (1, 2) turns (CH2021 Prop 1.10). We prune tubes with rotation > 2.

**Mathematical conditions:**
1. `p_start` is a convex polygon (intersection of start 2-face with tube constraints)
2. `p_end = flow_map(p_start) ∩ (end 2-face polygon)`
3. For any start point `s ∈ p_start`, there exists a unique trajectory ending at `flow_map(s)`
4. `action_func(s)` gives the action of that trajectory
5. `rotation` is constant over all trajectories in the tube (depends only on combinatorics)

**Why action is affine in starting position:** This follows from elementary algebra, not contact geometry:

1. **Reeb flow is linear:** On facet with normal \(n\), the flow is \(p(t) = p_0 + t \cdot R_n\) where \(R_n\) is the Reeb vector.

2. **Exit time is affine in starting position:** To exit facet \(n\) and enter facet \(n'\), solve \(\langle n', p(t) \rangle = d'\):
   \[t_{\text{exit}} = \frac{d' - \langle n', p_0 \rangle}{\langle n', R_n \rangle}\]
   This is affine in \(p_0\) (the denominator is constant for a given facet pair).

3. **Segment action = segment time:** For Reeb flow, \(A(\gamma) = T\) (action equals period). Each segment contributes \(t_{\text{exit}} - t_{\text{entry}}\).

4. **Composition preserves affinity:** The exit point \(p(t_{\text{exit}})\) is affine in \(p_0\). By induction, all breakpoints are affine in the initial starting position.

5. **Sum of affine functions is affine:** Total action = \(\sum_k t_k(p_0)\) where each \(t_k\) is affine in \(p_0\).

Therefore `action_func` is representable as \(f(x) = \langle g, x \rangle + c\) for some gradient \(g\) and constant \(c\).

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

**Action lower bound** (for branch-and-bound pruning):

The action function is affine over the start polygon: `action(s) = ⟨g, s⟩ + c`. To find the minimum action over the convex polygon `p_start`, we minimize an affine function over a convex set. For a convex polygon, the minimum occurs at a vertex.

```rust
impl Tube {
    fn action_lower_bound(&self) -> f64 {
        // Minimum of affine function over convex polygon = minimum over vertices
        self.p_start.vertices.iter()
            .map(|v| self.action_func.gradient.dot(v) + self.action_func.constant)
            .fold(f64::INFINITY, f64::min)
    }
}
```

**Note:** For empty tubes (`p_start.vertices.is_empty()`), return `f64::INFINITY` (already pruned). This method is O(n) where n = number of vertices in `p_start`, which is typically small (≤ 10).

---

### 2.10 Tube Extension

#### Computing Facet Flow

The function `compute_facet_flow` computes the affine map and time function for flowing along a facet from one 2-face to the next. This is the core geometric computation of the tube algorithm.

**Geometry:** A point \(p\) on 2-face \(F_{\text{prev}} \cap F_{\text{curr}}\) flows along facet \(F_{\text{curr}}\) with Reeb velocity \(R_{\text{curr}}\) until hitting 2-face \(F_{\text{curr}} \cap F_{\text{next}}\).

**Time computation:** The exit condition is \(\langle q, n_{\text{next}} \rangle = h_{\text{next}}\) where \(q = p + t \cdot R_{\text{curr}}\). Solving:
\[
t = \frac{h_{\text{next}} - \langle p, n_{\text{next}} \rangle}{\langle R_{\text{curr}}, n_{\text{next}} \rangle}
\]

Note: \(\langle R_{\text{curr}}, n_{\text{next}} \rangle \neq 0\) for non-Lagrangian 2-faces (guaranteed by flow direction).

```rust
fn compute_facet_flow(
    tube: &Tube,                    // Need previous facet from facet_sequence
    next_facet: usize,
    polytope_data: &PolytopeData,
) -> (AffineMap2D, AffineFunc) {
    // Extract facet indices
    let seq = &tube.facet_sequence;
    let prev_facet = seq[seq.len() - 2];    // i_{k}
    let curr_facet = seq[seq.len() - 1];    // i_{k+1}, the facet we flow along

    // Get 2-faces with their enriched data
    let entry_2face = polytope_data.get_two_face_enriched(prev_facet, curr_facet);
    let exit_2face = polytope_data.get_two_face_enriched(curr_facet, next_facet);

    // Get Reeb vector on current facet
    let r_curr = polytope_data.reeb_vector(curr_facet);    // R_{curr} = (2/h_{curr}) * J * n_{curr}
    let n_next = polytope_data.normal(next_facet);
    let h_next = polytope_data.height(next_facet);

    // Denominator of time formula: ⟨R_curr, n_next⟩
    let r_dot_n = r_curr.dot(&n_next);
    debug_assert!(r_dot_n.abs() > EPS, "Lagrangian 2-face or degenerate");

    // For a point p_2d in entry 2-face coordinates:
    // 1. Convert to 4D: p_4d = untrivialize(entry_triv_normal, p_2d) + centroid_entry
    // 2. Compute time: t = (h_next - ⟨p_4d, n_next⟩) / ⟨R_curr, n_next⟩
    // 3. Flow: q_4d = p_4d + t * R_curr
    // 4. Convert to exit coords: q_2d = trivialize(exit_triv_normal, q_4d - centroid_exit)
    //
    // IMPORTANT: Per CH2021 convention (§1.10), trivialization uses the EXIT facet's normal.
    // - Entry 2-face F_{prev,curr} is trivialized with n_curr (we're entering curr)
    // - Exit 2-face F_{curr,next} is trivialized with n_next (we're entering next)
    // These are stored in TwoFaceEnriched.exit_normal.
    //
    // <!-- NEEDS VERIFICATION: If bugs occur, check this normal convention first. -->

    // UPDATED: Use explicit basis vectors from §1.10.1 instead of the wrong
    // untrivialize formula. The basis vectors lie IN the 2-face tangent space.
    let b_entry = entry_2face.basis_exit;  // [bExit₁, bExit₂] for entry 2-face
    let b_exit = exit_2face.basis_exit;    // [bExit₁, bExit₂] for exit 2-face
    let c_entry = entry_2face.centroid_4d;
    let c_exit = exit_2face.centroid_4d;

    // For trivialization we still need QUAT_J and QUAT_K applied to normals
    let exit_triv_normal = &exit_2face.exit_normal;
    let jn_exit = QUAT_J * exit_triv_normal;
    let kn_exit = QUAT_K * exit_triv_normal;

    // Build the affine map and time function
    //
    // For p_2d = (a, b):
    //   p_4d = a * J*entry_triv_normal + b * K*entry_triv_normal + c_entry
    //   ⟨p_4d, n_next⟩ = a * ⟨J*entry_triv_normal, n_next⟩ + b * ⟨K*entry_triv_normal, n_next⟩ + ⟨c_entry, n_next⟩
    //
    //   t = (h_next - ⟨p_4d, n_next⟩) / r_dot_n
    //     = (h_next - ⟨c_entry, n_next⟩) / r_dot_n
    //       - (a * ⟨J*entry_triv_normal, n_next⟩ + b * ⟨K*entry_triv_normal, n_next⟩) / r_dot_n
    //
    // Time function: t(p_2d) = t_const + ⟨t_grad, p_2d⟩
    let t_const = (h_next - c_entry.dot(&n_next)) / r_dot_n;
    let t_grad = Vector2::new(
        -j_n_entry.dot(&n_next) / r_dot_n,
        -k_n_entry.dot(&n_next) / r_dot_n,
    );
    let time_func = AffineFunc { gradient: t_grad, constant: t_const };

    // Flow map: q_4d = p_4d + t * R_curr
    //   q_4d - c_exit = (p_4d - c_entry) + (c_entry - c_exit) + t * R_curr
    //
    // Trivialize in exit coordinates:
    //   q_2d[0] = ⟨q_4d - c_exit, J*exit_triv_normal⟩
    //   q_2d[1] = ⟨q_4d - c_exit, K*exit_triv_normal⟩

    // Build 2x2 matrix A and offset b for q_2d = A * p_2d + b
    //
    // Components of A come from how (a, b) → p_4d → q_4d → q_2d
    // Including the time dependence on p_2d

    // Direct term: trivialize(exit_triv_normal, untrivialize(entry_triv_normal, e_i))
    // This is the transition matrix ψ from section 1.11
    let psi = compute_transition_matrix(entry_triv_normal, exit_triv_normal);

    // Time-dependent term: derivative of (t * R_curr) w.r.t. p_2d, trivialized
    // dt/d(p_2d) = t_grad
    // d(t * R_curr)/d(p_2d) = R_curr ⊗ t_grad (outer product)
    // Trivialized: [⟨R_curr, J*exit_triv_normal⟩, ⟨R_curr, K*exit_triv_normal⟩] ⊗ t_grad
    let r_triv = Vector2::new(r_curr.dot(&j_n_exit), r_curr.dot(&k_n_exit));

    // Matrix: A = ψ + r_triv ⊗ t_grad
    let a_matrix = psi + r_triv * t_grad.transpose();

    // Offset: b = trivialize(exit_triv_normal, c_entry - c_exit + t_const * R_curr)
    let delta_c = c_entry - c_exit + r_curr * t_const;
    let b_offset = Vector2::new(delta_c.dot(&j_n_exit), delta_c.dot(&k_n_exit));

    let flow_map = AffineMap2D { matrix: a_matrix, offset: b_offset };

    (flow_map, time_func)
}
```

**Assertions:**
```rust
// Flow map is symplectic (area-preserving)
assert!((flow_map.matrix.determinant() - 1.0).abs() < EPS);

// Time is positive for valid flow direction
// (may be negative if we're flowing the wrong way, which should be caught by empty intersection)
```

#### Extending a Tube

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
    let (phi, time_func) = compute_facet_flow(tube, next_facet, polytope_data);

    // New endpoint set (standard: Sutherland-Hodgman for convex polygon intersection)
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

To find closed Reeb orbits within a **closed tube** (see §2.8 for terminology), solve for fixed points of the flow map. Since start 2-face = end 2-face for a closed tube, the flow map \(\psi\) maps the start 2-face to itself, and fixed points correspond to periodic orbits.

To find closed orbits, solve for fixed points of the flow map:
\[
\psi(s) = s \quad \Leftrightarrow \quad (A - I) s = -b
\]

```rust
fn find_closed_orbits(tube: &Tube) -> Vec<(f64, Vector2<f64>)> {
    // Solve (A - I) s = -b
    let a_minus_i = tube.flow_map.matrix - Matrix2::identity();
    let neg_b = -tube.flow_map.offset;

    let det = a_minus_i.determinant();

    if det.abs() < EPS {
        // Near-singular case: the flow map (A - I) is nearly singular.
        // In the generic case, there is 0 or 1 fixed point per tube (see review §0.6).
        // Near-singularity indicates either:
        //   (a) A degenerate polytope (multiple fixed points), or
        //   (b) Numerical instability near a bifurcation.
        // Do not silently assume genericity; raise a runtime error.
        panic!(
            "Near-singular flow map in tube closure: det(A - I) = {:.2e}. \
             This may indicate a degenerate polytope or numerical instability. \
             Facet sequence: {:?}",
            det, tube.facet_sequence
        );
    }

    // Unique fixed point: s = (A - I)^{-1} (-b)
    let s = a_minus_i.try_inverse().unwrap() * neg_b;

    // Check if fixed point is in p_start (standard: winding number or crossing number test)
    if !point_in_polygon(&s, &tube.p_start) {
        return vec![];
    }

    let action = tube.action_func.gradient.dot(&s) + tube.action_func.constant;
    vec![(action, s)]
}
```

**Assertions:**
```rust
// Fixed point satisfies flow_map(s) = s
let s_mapped = tube.flow_map.matrix * fixed_point + tube.flow_map.offset;
assert!((s_mapped - fixed_point).norm() < EPS);

// Fixed point is in the valid start region
assert!(point_in_polygon(&fixed_point, &tube.p_start));
```

---

### 2.12 Reconstruction: 2D Coordinates to 4D Orbit

Given a closed orbit in 2D trivialized coordinates, reconstruct the 4D orbit.

**Coordinate conversion:** To convert a 2D trivialized point back to 4D:
```rust
fn untrivialize_point(
    point_2d: &Vector2<f64>,
    two_face: &TwoFaceEnriched,
) -> Vector4<f64> {
    // The 2D coordinates are relative to the 2-face's centroid
    // using the trivialization basis {J*n_exit, K*n_exit} (CH2021 convention)
    let n_exit = two_face.exit_normal;
    let offset_4d = untrivialize(&n_exit, point_2d);
    two_face.centroid_4d + offset_4d
}
```

**Full reconstruction:**
```rust
fn reconstruct_4d_orbit(
    fixed_point_2d: &Vector2<f64>,
    tube: &Tube,
    polytope_data: &PolytopeData,
) -> ClosedReebOrbit {
    let seq = &tube.facet_sequence;
    let n_segments = seq.len() - 2;  // Number of facet segments

    // Start from the 2D fixed point on the start 2-face
    let start_two_face = polytope_data.get_two_face_enriched(seq[0], seq[1]);
    let start_4d = untrivialize_point(fixed_point_2d, &start_two_face);

    // Trace through each facet to get breakpoints
    let mut breakpoints = vec![start_4d];
    let mut current_2d = *fixed_point_2d;

    // Build partial tube to track coordinate transformations
    for k in 1..=n_segments {
        // Current 2-face is F_{seq[k-1]} ∩ F_{seq[k]}
        // Next 2-face is F_{seq[k]} ∩ F_{seq[k+1]}

        // Get flow map for this segment
        let partial_tube = Tube {
            facet_sequence: seq[0..=k].to_vec(),
            ..tube.clone()  // other fields not used
        };
        let (phi, _) = compute_facet_flow(&partial_tube, seq[k + 1], polytope_data);

        // Apply flow to get exit point in next 2-face coordinates
        current_2d = phi.matrix * current_2d + phi.offset;

        // Convert to 4D
        let exit_two_face = polytope_data.get_two_face_enriched(seq[k], seq[k + 1]);
        let exit_4d = untrivialize_point(&current_2d, &exit_two_face);
        breakpoints.push(exit_4d);
    }

    // Close the orbit (should match start_4d)
    debug_assert!(
        (breakpoints.last().unwrap() - &start_4d).norm() < EPS,
        "Orbit failed to close"
    );

    // Compute segment facets: segment k flows along facet seq[k+1]
    let segment_facets: Vec<usize> = (0..n_segments)
        .map(|k| seq[k + 1])
        .collect();

    // Compute segment times from displacement and Reeb velocity
    let segment_times: Vec<f64> = (0..n_segments)
        .map(|k| {
            let facet_idx = segment_facets[k];
            let displacement = &breakpoints[k + 1] - &breakpoints[k];
            let reeb = polytope_data.reeb_vector(facet_idx);

            // Time = |displacement| / |Reeb| = ⟨displacement, Reeb⟩ / |Reeb|²
            // Since displacement = t * Reeb, we have t = displacement · Reeb / |Reeb|²
            displacement.dot(&reeb) / reeb.norm_squared()
        })
        .collect();

    let period: f64 = segment_times.iter().sum();

    ClosedReebOrbit {
        period,
        breakpoints,
        segment_facets,
        segment_times,
    }
}
```

**Assertions:**
```rust
// All segment times are positive
assert!(segment_times.iter().all(|&t| t > 0.0));

// Segment displacements match Reeb velocities
for k in 0..n_segments {
    let displacement = &breakpoints[k + 1] - &breakpoints[k];
    let expected = polytope_data.reeb_vector(segment_facets[k]) * segment_times[k];
    assert!((displacement - expected).norm() < EPS);
}

// Period equals action (for closed Reeb orbits)
let action = action_of_closed_polygon(&breakpoints);
assert!((period - action).abs() < EPS * period);
```

---

### 2.13 Validity Checks for Reeb Orbits

Comprehensive validation for computed orbits:

```rust
impl ClosedReebOrbit {
    fn validate(&self, hrep: &PolytopeHRep) -> Result<(), ValidationError> {
        // 1. Closure
        if (self.breakpoints.last().unwrap() - &self.breakpoints[0]).norm() > EPS {
            return Err(ValidationError::NotClosed);
        }

        // 2. All breakpoints on boundary
        for (k, p) in self.breakpoints.iter().enumerate() {
            if !is_on_boundary(p, hrep) {
                return Err(ValidationError::BreakpointNotOnBoundary(k));
            }
        }

        // 3. Segments lie on claimed facets
        for k in 0..self.segment_facets.len() {
            let i = self.segment_facets[k];
            let p_start = &self.breakpoints[k];
            let p_end = &self.breakpoints[k + 1];

            if (hrep.normals[i].dot(p_start) - hrep.heights[i]).abs() > EPS {
                return Err(ValidationError::SegmentNotOnFacet(k, "start"));
            }
            if (hrep.normals[i].dot(p_end) - hrep.heights[i]).abs() > EPS {
                return Err(ValidationError::SegmentNotOnFacet(k, "end"));
            }
        }

        // 4. Velocities match Reeb vectors
        for k in 0..self.segment_facets.len() {
            let i = self.segment_facets[k];
            let displacement = &self.breakpoints[k + 1] - &self.breakpoints[k];
            let velocity = displacement / self.segment_times[k];
            let reeb = (J_MATRIX * hrep.normals[i]) * (2.0 / hrep.heights[i]);

            if (velocity - reeb).norm() > EPS * reeb.norm() {
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

| Algorithm | Domain | Notes |
|-----------|--------|-------|
| Billiard | Lagrangian products \(K_1 \times K_2\) | Most reliable; see Rudolf 2022 Thm 4 |
| HK2017 | All polytopes | Limited to ~10 facets in practice |
| Tube | Non-Lagrangian polytopes | Requires no Lagrangian 2-faces; see CH2021 |

**Complexity note:** Precise complexity analysis is not a priority for this implementation. The algorithms are exponential in the number of facets (factorial for permutation enumeration). For practical use, Billiard is fastest on Lagrangian products, HK2017 is limited by permutation enumeration, and Tube is limited by the branch-and-bound search space.

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

**Source:** This thesis (Stöhler 2026), Section \ref{sec:algo-ours}. The algorithm extends CH2021's mathematical framework (Reeb dynamics on polytopes, linear flows, symplectic flow graphs) with a branch-and-bound search over "tubes" — sets of trajectories sharing a combinatorial class. The "tube" terminology and the specific algorithmic structure are original to this thesis.

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

### 3.5 Known Limitations and Open Issues

**Algorithm coverage gaps:**

| Polytope Type | 2-Face Character | Status |
|---------------|------------------|--------|
| Lagrangian products | ALL Lagrangian | ✓ Billiard, HK2017 |
| Non-Lagrangian | NO Lagrangian | ✓ Tube, HK2017 |
| Mixed | SOME Lagrangian | ✗ No algorithm designed |

**HK2017 QP solver incompleteness:**

The quadratic form Q(σ, β) is **indefinite** (the symplectic form has mixed signs). The maximum may occur at:
- Vertices (0D faces) of the feasible polytope
- Edges (1D faces)
- Higher-dimensional face interiors

A complete implementation requires a global QCQP solver or exhaustive face enumeration. The current approach (checking only vertices) is **incomplete** and may miss the true maximum.

**Pentagon × RotatedPentagon bug:**

The billiard algorithm returns capacity ≈ 2.127 for the HK-O counterexample pentagon product, but the correct value is ≈ 3.441 (HK-O 2024 Prop 1). This is a known bug documented in `mathematical-claims.md`. Investigation is ongoing.

**Missing tube algorithm test case:**

No polytope with verified capacity and NO Lagrangian 2-faces is currently in the test suite. The cross-polytope `conv{±eᵢ}` is a candidate (verify no Lagrangian 2-faces first), but its capacity is not independently known.

**Tolerance philosophy (deferred):**

The relationship between tolerances (EPS, EPS_LAGRANGIAN, EPS_ROTATION, etc.) is not rigorously analyzed. Current approach: detect when numerics go wrong and error out, rather than theorize tolerance choices in advance.

---

## 4. Test Cases and Verification Properties

This section lists mathematical properties that tests should verify. If any test fails, the code contains a bug (does not correspond to the mathematical "proof").

### 4.0 Testing Philosophy

**Language choice:** Tests can be written in Python and/or Rust. Each has tradeoffs:

| Aspect | Rust | Python |
|--------|------|--------|
| DevOps friction | Higher (compile times) | Lower (immediate execution) |
| CPU performance | Faster | Slower (but FFI bridges to Rust) |
| Ease of writing | More boilerplate | More concise |
| Libraries | nalgebra, proptest | numpy, hypothesis, pytest |
| Debugging | println!, debugger | print, pdb, rich tracebacks |

**Guidance:**
- Use Python for exploratory tests, visualization, hypothesis-based property tests
- Use Rust for performance-critical tests, tests that need deep integration with internals
- Code duplication is acceptable while iterating — clean up later
- Tests need not be perfect on first write; iterate like algorithm code

**Optimization:**
- Don't optimize prematurely
- Only optimize after identifying a need AND profiling to find hotspots
- "Fast enough" is good enough

**Debugging approaches:**
- Print/log statements (quick and dirty)
- Debug assertions and invariant checks
- Interactive debuggers (Rust: lldb/gdb; Python: pdb/ipdb)
- Visualization (Python matplotlib/plotly for 2D projections)
- Property-based testing to find edge cases (hypothesis/proptest)

---

### 4.1 Ground Truth Capacity Values

| Polytope | \(c_{\text{EHZ}}\) | Source | Algorithms | Notes |
|----------|-----------|--------|------------|-------|
| Tesseract \([-1,1]^4\) | 4.0 | HK2017 Ex 4.6 | Billiard, HK2017 | Primary test case (Lagrangian product) |
| Rectangle \(2 \times 1\) product | 1.0 | Scaling | Billiard, HK2017 | Lagrangian product |
| Triangle × Triangle (r=1) | 1.5 | Computational | Billiard, HK2017 | Lagrangian product, circumradius 1, [NEEDS CITATION] |
| Pentagon × RotatedPentagon | 3.441 | HK-O 2024 Prop 1 | Billiard, HK2017 | Lagrangian product, counterexample to Viterbo |
| 4-Simplex (standard) | 0.25 | [UNVERIFIED] | HK2017 only | **WARNING:** conv{0, e₁, e₂, e₃, e₄} has 0 on boundary (invalid). Has Lagrangian 2-faces → Tube inapplicable. Citation "Y. Nir 2013" needs verification. |

**Algorithm applicability key:**
- **Billiard:** Only for Lagrangian products (K₁ × K₂ with q/p separation)
- **HK2017:** All polytopes (but QP solver is incomplete for indefinite case)
- **Tube:** Only for polytopes with NO Lagrangian 2-faces

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
        assert!(is_on_boundary(p, K), "Breakpoint not on boundary");
    }
}
```

**4.3.2 Segments on facets:**
```rust
fn test_segments_on_facets(orbit: &ClosedReebOrbit, K: &PolytopeHRep) {
    for k in 0..orbit.segment_facets.len() {
        let i = orbit.segment_facets[k];
        let p0 = &orbit.breakpoints[k];
        let p1 = &orbit.breakpoints[k + 1];

        // Both endpoints on the claimed facet
        assert!((K.normals[i].dot(p0) - K.heights[i]).abs() < EPS);
        assert!((K.normals[i].dot(p1) - K.heights[i]).abs() < EPS);
    }
}
```

**4.3.3 Velocities match Reeb vectors (differential inclusion):**
```rust
fn test_reeb_velocity(orbit: &ClosedReebOrbit, K: &PolytopeHRep) {
    for k in 0..orbit.segment_facets.len() {
        let i = orbit.segment_facets[k];
        let displacement = &orbit.breakpoints[k + 1] - &orbit.breakpoints[k];
        let velocity = displacement / orbit.segment_times[k];
        let reeb = (J_MATRIX * K.normals[i]) * (2.0 / K.heights[i]);

        assert!((velocity - reeb).norm() < EPS * reeb.norm(),
            "Velocity on segment {} doesn't match Reeb vector", k);
    }
}
```

**4.3.4 Orbit closure:**
```rust
fn test_orbit_closure(orbit: &ClosedReebOrbit) {
    let first = &orbit.breakpoints[0];
    let last = &orbit.breakpoints[orbit.breakpoints.len() - 1];
    assert!((first - last).norm() < EPS, "Orbit not closed");
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
    let u = Vector4::new(1.0, 2.0, 3.0, 4.0);
    let v = Vector4::new(5.0, 6.0, 7.0, 8.0);
    let w = Vector4::new(9.0, 10.0, 11.0, 12.0);

    // Antisymmetry
    assert!((symplectic_form(&u, &v) + symplectic_form(&v, &u)).abs() < EPS);

    // Bilinearity
    assert!((symplectic_form(&(u + v), &w) - symplectic_form(&u, &w) - symplectic_form(&v, &w)).abs() < EPS);

    // Standard basis values
    let e1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
    let e2 = Vector4::new(0.0, 1.0, 0.0, 0.0);
    let e3 = Vector4::new(0.0, 0.0, 1.0, 0.0);
    let e4 = Vector4::new(0.0, 0.0, 0.0, 1.0);
    assert!((symplectic_form(&e1, &e3) - 1.0).abs() < EPS);  // ω(e1, e3) = 1
    assert!((symplectic_form(&e2, &e4) - 1.0).abs() < EPS);  // ω(e2, e4) = 1
    assert!(symplectic_form(&e1, &e2).abs() < EPS);          // ω(e1, e2) = 0
}
```

**4.5.2 Quaternion relations:**
```rust
#[test]
fn test_quaternion_relations() {
    let v = random_unit_vector();

    // i² = j² = k² = -I (quaternion relations)
    assert!((QUAT_I * QUAT_I * v + v).norm() < EPS);
    assert!((QUAT_J * QUAT_J * v + v).norm() < EPS);
    assert!((QUAT_K * QUAT_K * v + v).norm() < EPS);

    // ij = k, jk = i, ki = j
    assert!(((QUAT_I * QUAT_J - QUAT_K) * v).norm() < EPS);
    assert!(((QUAT_J * QUAT_K - QUAT_I) * v).norm() < EPS);
    assert!(((QUAT_K * QUAT_I - QUAT_J) * v).norm() < EPS);
}
```

**4.5.3 Transition matrix is symplectic:**
```rust
#[test]
fn test_transition_matrix_symplectic() {
    for two_face in &polytope_data.two_faces {
        let psi = &two_face.transition_matrix;

        // det(ψ) = 1
        assert!((psi.determinant() - 1.0).abs() < EPS);

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

**4.5.5 Cross-polytope trivialization test (regression for bug found 2026-01-26):**

This test exposed the original trivialization bug where the inverse formula was wrong.

```rust
#[test]
fn test_cross_polytope_trivialization() {
    // Adjacent facet normals from 16-cell (cross-polytope)
    let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
    let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

    // Compute basis vectors using the CORRECT method (§1.10.1)
    let b_exit = compute_exit_basis(&n_entry, &n_exit);
    let b_entry = compute_entry_basis(&n_entry, &n_exit);

    // Basis vectors must lie in 2-face tangent space (perp to BOTH normals)
    for b in &b_exit {
        assert!(b.dot(&n_entry).abs() < EPS, "bExit not perp to n_entry");
        assert!(b.dot(&n_exit).abs() < EPS, "bExit not perp to n_exit");
    }
    for b in &b_entry {
        assert!(b.dot(&n_entry).abs() < EPS, "bEntry not perp to n_entry");
        assert!(b.dot(&n_exit).abs() < EPS, "bEntry not perp to n_exit");
    }

    // Compute transition matrix both ways and verify they match
    let psi_basis = compute_transition_matrix_basis(&b_entry, &n_exit);
    let psi_ch2021 = compute_transition_matrix_ch2021(&n_entry, &n_exit);
    assert!((psi_basis - psi_ch2021).norm() < EPS, "Methods disagree!");

    // Transition matrix must be symplectic
    assert!((psi_basis.determinant() - 1.0).abs() < EPS,
        "det(ψ) = {}, expected 1.0", psi_basis.determinant());

    // Trace must equal 2⟨n_entry, n_exit⟩
    let expected_trace = 2.0 * n_entry.dot(&n_exit);
    assert!((psi_basis.trace() - expected_trace).abs() < EPS,
        "tr(ψ) = {}, expected {}", psi_basis.trace(), expected_trace);

    // Rotation number should be valid
    let rho = psi_basis.trace().abs().min(2.0 - EPS);
    let rotation = (0.5 * rho).acos() / (2.0 * std::f64::consts::PI);
    assert!(rotation > 0.0 && rotation < 0.5);
}
```

---

### 4.6 Tube Algorithm Specific Tests

**4.6.1 Flow map consistency:**
```rust
fn test_tube_flow_map(tube: &Tube, start_point: &Vector2<f64>) {
    // Trace the trajectory step by step
    let traced_end = trace_trajectory_stepwise(tube, start_point);

    // Compare with flow map
    let mapped_end = tube.flow_map.matrix * start_point + tube.flow_map.offset;

    assert!((traced_end - mapped_end).norm() < EPS);
}
```

**4.6.2 Action function consistency:**
```rust
fn test_tube_action_func(tube: &Tube, start_point: &Vector2<f64>) {
    // Trace trajectory and sum segment times
    let traced_action = trace_and_sum_action(tube, start_point);

    // Compare with action function
    let computed_action = tube.action_func.gradient.dot(start_point) + tube.action_func.constant;

    assert!((traced_action - computed_action).abs() < EPS);
}
```

**4.6.3 Closed orbit is actually closed:**
```rust
fn test_closed_orbit_is_fixed_point(orbit_2d: &Vector2<f64>, tube: &Tube) {
    let mapped = tube.flow_map.matrix * orbit_2d + tube.flow_map.offset;
    assert!((orbit_2d - mapped).norm() < EPS,
        "Claimed closed orbit is not a fixed point of flow map");
}
```

**4.6.4 Flow map is symplectic (area-preserving):**
```rust
fn test_flow_map_symplectic(tube: &Tube) {
    // For 2D symplectic maps, det(A) = 1
    let det = tube.flow_map.matrix.determinant();
    assert!((det - 1.0).abs() < EPS,
        "Flow map not symplectic: det = {}", det);
}
```

**4.6.5 Root tube initialization:**
```rust
fn test_root_tube_valid(two_face: &TwoFaceEnriched) {
    let root = create_root_tube(two_face);

    // p_start has positive area (non-empty)
    assert!(polygon_area(&root.p_start) > EPS,
        "Root tube p_start is empty or degenerate");

    // Flow map is identity
    assert!((root.flow_map.matrix - Matrix2::identity()).norm() < EPS);
    assert!(root.flow_map.offset.norm() < EPS);

    // Action function is zero
    assert!(root.action_func.gradient.norm() < EPS);
    assert!(root.action_func.constant.abs() < EPS);

    // Rotation is zero
    assert!(root.rotation.abs() < EPS);
}
```

**4.6.6 Tube extension preserves symplecticity:**
```rust
fn test_tube_extension_symplectic(tube: &Tube, extended: &Tube) {
    // Both should have det(A) = 1
    assert!((tube.flow_map.matrix.determinant() - 1.0).abs() < EPS);
    assert!((extended.flow_map.matrix.determinant() - 1.0).abs() < EPS);

    // Rotation should increase by a positive amount in (0, 0.5)
    let delta_rotation = extended.rotation - tube.rotation;
    assert!(delta_rotation > 0.0 && delta_rotation < 0.5,
        "Invalid rotation increment: {}", delta_rotation);
}
```

**4.6.7 Independent Reeb flow verification:**
```rust
fn test_trajectory_no_intermediate_crossings(
    orbit: &ClosedReebOrbit,
    polytope_data: &PolytopeData,
) {
    // For each segment, verify the trajectory doesn't cross any other facet
    for k in 0..orbit.segment_facets.len() {
        let facet = orbit.segment_facets[k];
        let start = &orbit.breakpoints[k];
        let end = &orbit.breakpoints[k + 1];
        let reeb = polytope_data.reeb_vector(facet);

        // Check midpoint is still on the claimed facet
        let mid = (start + end) / 2.0;
        let h = polytope_data.heights[facet];
        let n = &polytope_data.normals[facet];
        assert!((n.dot(&mid) - h).abs() < EPS,
            "Segment {} midpoint not on facet", k);

        // Check midpoint doesn't violate any other facet constraint
        for (j, (nj, &hj)) in polytope_data.normals.iter()
            .zip(&polytope_data.heights).enumerate()
        {
            if j != facet {
                assert!(nj.dot(&mid) <= hj + EPS,
                    "Segment {} crosses facet {}", k, j);
            }
        }
    }
}
```

**4.6.8 Near-singular detection:**
```rust
#[test]
fn test_near_singular_raises_error() {
    // Construct a tube with nearly-singular flow map (det(A-I) ≈ 0)
    // This should panic rather than silently return wrong results
    let tube = Tube {
        flow_map: AffineMap2D {
            matrix: Matrix2::identity() + Matrix2::new(1e-12, 0.0, 0.0, 1e-12),
            offset: Vector2::new(0.1, 0.1),
        },
        // ... other fields
    };

    let result = std::panic::catch_unwind(|| find_closed_orbits(&tube));
    assert!(result.is_err(), "Should panic on near-singular flow map");
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
            assert!(n.dot(v) <= h + EPS);
        }
    }

    // Every vertex is tight on exactly dim=4 facets (for simple polytopes)
    for v in &K.vertices {
        let tight_count = K.normals.iter().zip(&K.heights)
            .filter(|(n, &h)| (n.dot(v) - h).abs() < EPS)
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
            assert!((data.normals[two_face.i].dot(v) - data.heights[two_face.i]).abs() < EPS);
            assert!((data.normals[two_face.j].dot(v) - data.heights[two_face.j]).abs() < EPS);
        }

        // Lagrangian classification is correct
        let omega = symplectic_form(&data.normals[two_face.i], &data.normals[two_face.j]);
        assert_eq!(omega.abs() < EPS_LAGRANGIAN, two_face.is_lagrangian);
    }
}
```

---

### 4.8 Continuity Tests (Perturbed Lagrangian Products)

A powerful testing strategy: perturb a Lagrangian product (with known capacity from Billiard algorithm) to break the Lagrangian structure, then run the Tube algorithm. The result should be close to the original capacity.

**Rationale:** Capacity is continuous in the Hausdorff metric, so small perturbations should yield small capacity changes. This tests the Tube algorithm on "nearly Lagrangian" polytopes where we have approximate ground truth.

```rust
#[test]
fn test_tube_vs_billiard_perturbed() {
    // 1. Start with a Lagrangian product
    let K_lagrangian = tesseract();
    let c_billiard = billiard_capacity(&K_lagrangian);

    // 2. Apply a small symplectic perturbation that breaks Lagrangian structure
    // Example: small shear (q, p) → (q, p + εSq) where S is symmetric
    let epsilon = 0.01;
    let shear = symplectic_shear(epsilon);
    let K_perturbed = apply_symplectomorphism(&K_lagrangian, &shear);

    // 3. Verify no Lagrangian 2-faces (tube algorithm applicable)
    let data = preprocess_polytope(&K_perturbed).unwrap();
    assert!(!data.has_lagrangian_two_faces(),
        "Perturbation didn't break Lagrangian structure");

    // 4. Run tube algorithm
    let c_tube = tube_capacity(&K_perturbed).unwrap();

    // 5. Check continuity: |c_tube - c_billiard| should be O(ε²)
    // (Capacity is symplectic invariant, but H-rep changes under shear affect geometry)
    let relative_diff = (c_tube - c_billiard).abs() / c_billiard;
    assert!(relative_diff < 0.1,
        "Tube capacity {} differs from billiard {} by {:.1}%",
        c_tube, c_billiard, relative_diff * 100.0);
}

fn symplectic_shear(epsilon: f64) -> Matrix4<f64> {
    // Shear: (q1, q2, p1, p2) → (q1, q2, p1 + ε*q1, p2 + ε*q2)
    // This is symplectic (det = 1, preserves ω)
    let mut m = Matrix4::identity();
    m[(2, 0)] = epsilon;
    m[(3, 1)] = epsilon;
    m
}
```

**Testing near-Lagrangian numerical stability:**

```rust
#[test]
fn test_near_lagrangian_stability() {
    // Construct polytope with ω(n_i, n_j) ≈ 1e-6 for some 2-face
    // This is "almost Lagrangian" and may stress numerical precision

    for epsilon in [1e-3, 1e-6, 1e-9] {
        let K = nearly_lagrangian_polytope(epsilon);
        let data = preprocess_polytope(&K);

        match data {
            Ok(d) if d.has_lagrangian_two_faces() => {
                // Correctly detected as Lagrangian at this threshold
            }
            Ok(d) => {
                // Non-Lagrangian: tube should work or fail gracefully
                let result = tube_capacity(&K);
                // Either succeeds or returns meaningful error
                assert!(result.is_ok() || matches!(result, Err(Error::NumericalInstability)));
            }
            Err(_) => {
                // Preprocessing failed (acceptable for very small epsilon)
            }
        }
    }
}
```

---

### 4.9 Falsification Test Strategy

Tests should be designed to **catch bugs**, not just confirm correctness. The following tables list specific tests organized by what failure they would reveal.

**4.9.1 Trivialization Tests (§1.10):**

| Test | What Failure Reveals |
|------|---------------------|
| `trivialize(n, untrivialize(n, v)) == v` for random v | Round-trip broken |
| `untrivialize(n, trivialize(n, w)) == w` for w ⊥ n | Inverse broken on tangent vectors |
| `ω_4D(v1, v2) == ω_2D(τ(v1), τ(v2))` for v1, v2 ⊥ n | Symplectic preservation broken |
| Near-Lagrangian: ω(n_i, n_j) = 1e-8, check τ still works | Numerical instability near degeneracy |
| n_i ≈ n_j (nearly parallel normals) | Edge case in transition matrix |

**4.9.2 Transition Matrix Tests (§1.11):**

| Test | What Failure Reveals |
|------|---------------------|
| `det(ψ) == 1` for all 2-faces | Symplecticity broken |
| `\|tr(ψ)\| < 2` iff `\|ω(n_i, n_j)\| > EPS` | Lagrangian classification inconsistent |
| `ψ_ji == ψ_ij^{-1}` | Direction dependence wrong |
| Compose ψ around closed facet loop = identity? | Global consistency |

**4.9.3 Flow Map Tests (§2.10):**

| Test | What Failure Reveals |
|------|---------------------|
| `det(flow_map.matrix) == 1` after each extension | Area preservation broken |
| `flow_map(p)` actually lands on exit 2-face | Flow computation wrong |
| Time function gives positive time for valid flow direction | Sign error |
| Time ≈ 0: point near exit 2-face already | Edge case |
| Time very large: point far from exit 2-face | Numerical overflow |

**4.9.4 Fixed Point Tests (§2.11):**

| Test | What Failure Reveals |
|------|---------------------|
| `flow_map(fixed_point) == fixed_point` within EPS | Fixed point computation wrong |
| `point_in_polygon(fixed_point, p_start)` | Containment test wrong |
| Fixed point on polygon edge | Boundary case |
| Near-singular: `\|det(A - I)\| < 1e-10` → error raised | Silent failure on degeneracy |

**4.9.5 4D Reconstruction Tests (§2.12-2.13):**

| Test | What Failure Reveals |
|------|---------------------|
| `‖breakpoints[0] - breakpoints[last]‖ < EPS` | Orbit doesn't close |
| Each breakpoint on claimed 2-face | Reconstruction wrong |
| Each segment midpoint on claimed facet | Segment leaves facet |
| `velocity_k == R_{facet_k}` | Reeb velocity wrong |
| `Σ segment_times == action_of_polygon(breakpoints)` | Action computation inconsistent |
| Independent Reeb flow integration hits breakpoint[k+1] | Combinatorics wrong |

**4.9.6 Polytope Edge Cases:**

| Polytope | What It Tests |
|----------|---------------|
| Tesseract `[-1,1]⁴` | Baseline (Lagrangian product, c=4) |
| Tesseract + symplectomorphism | Symplectic invariance |
| Tesseract scaled by λ=2 | Scaling axiom (c=16) |
| Tesseract perturbed to break Lagrangian | Tube on near-Lagrangian |
| Cross-polytope `conv{±eᵢ}` | Tube on non-product (verify no Lagrangian 2-faces first) |
| Random hull of 10 points | Generic polytope (reject if 0∉int or has Lagrangian 2-face) |
| Nearly coplanar facets | Numerical sensitivity |
| ω(n_i, n_j) ≈ 1e-6 | Stability near degeneracy |
| 5-facet polytope | Minimal case for 4D |

**4.9.7 Algorithm Agreement Tests:**

| Test | What Failure Reveals |
|------|---------------------|
| Lagrangian product: `billiard(K) == hk2017(K)` | Algorithm inconsistency |
| Perturbed Lagrangian: `tube(K') ≈ billiard(K)` | Continuity violation |
| Same polytope, different vertex order: same result | Order dependence bug |

**Cross-polytope as tube test candidate:**

The cross-polytope `conv{±e₁, ±e₂, ±e₃, ±e₄}` has:
- 0 in its interior ✓
- 16 facets with normals proportional to (±1,±1,±1,±1)

**Unit test: Cross-polytope has no Lagrangian 2-faces:**
```rust
#[test]
fn test_cross_polytope_no_lagrangian_2faces() {
    let cross = cross_polytope();
    let data = preprocess_polytope(&cross).unwrap();

    for two_face in &data.two_faces {
        let omega = symplectic_form(
            &data.normals[two_face.i],
            &data.normals[two_face.j]
        );
        assert!(
            omega.abs() > EPS_LAGRANGIAN,
            "Cross-polytope has Lagrangian 2-face F_{},{}: ω = {:.2e}",
            two_face.i, two_face.j, omega
        );
    }

    // If this test passes, cross-polytope is valid for tube algorithm testing
    assert!(!data.has_lagrangian_two_faces());
}
```

If this test passes, the cross-polytope provides a non-Lagrangian-product test case for the tube algorithm. Its capacity is not independently known, but we can verify orbit validity and algorithm consistency.

---

### 4.10 Test Fixture Definitions

**Tesseract:**
```rust
fn tesseract() -> PolytopeHRep {
    PolytopeHRep {
        normals: vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0), Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0), Vector4::new(0.0, -1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0), Vector4::new(0.0, 0.0, -1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0), Vector4::new(0.0, 0.0, 0.0, -1.0),
        ],
        heights: vec![1.0; 8],
    }
}
```

**Cross-polytope (for tube algorithm testing):**
```rust
fn cross_polytope() -> PolytopeHRep {
    // Cross-polytope = conv{±e₁, ±e₂, ±e₃, ±e₄}
    // Has 16 facets with normals (±1,±1,±1,±1)/2
    let mut normals = Vec::new();
    let mut heights = Vec::new();

    for s1 in [-1.0, 1.0] {
        for s2 in [-1.0, 1.0] {
            for s3 in [-1.0, 1.0] {
                for s4 in [-1.0, 1.0] {
                    let n = Vector4::new(s1, s2, s3, s4) / 2.0;  // normalize
                    normals.push(n);
                    heights.push(1.0);  // 0 at center, vertices at distance 1
                }
            }
        }
    }

    PolytopeHRep { normals, heights }
}
```

**Triangle × Triangle (equilateral, circumradius 1):**
```rust
fn triangle_product() -> LagrangianProductPolytope {
    use std::f64::consts::PI;
    let angles = [0.0, 2.0 * PI / 3.0, 4.0 * PI / 3.0];
    let vertices: Vec<Vector2<f64>> = angles.iter()
        .map(|&a| Vector2::new(a.cos(), a.sin()))
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
    use std::f64::consts::PI;
    let angles: Vec<f64> = (0..5).map(|i| 2.0 * PI * i as f64 / 5.0).collect();

    let pentagon_vertices: Vec<Vector2<f64>> = angles.iter()
        .map(|&a| Vector2::new(a.cos(), a.sin()))
        .collect();

    let rotated_vertices: Vec<Vector2<f64>> = angles.iter()
        .map(|&a| Vector2::new((a + PI/2.0).cos(), (a + PI/2.0).sin()))
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
- **HK2017:** Haim-Kislev, "On the Symplectic Size of Convex Polytopes" (arXiv:1712.03494, December 2017). Note: Some older documents may refer to this as "HK2019" (journal publication year); we use "HK2017" (arXiv year) consistently.
- **Rudolf 2022:** "The Minkowski Billiard Characterization of the EHZ-Capacity" (arXiv:2203.01718)

### Primary Sources (Ground Truth Values)

- **HK-O 2024:** Haim-Kislev & Ostrover, "A Counterexample to Viterbo's Conjecture" (arXiv:2405.16513)
- **Y. Nir 2013:** "On Closed Characteristics and Billiards in Convex Bodies" (thesis, Tel Aviv University)

### Textbooks

- **Hofer-Zehnder 1994:** "Symplectic Invariants and Hamiltonian Dynamics"
- **Schneider 2014:** "Convex Bodies: The Brunn-Minkowski Theory"
- **McDuff-Salamon 2017:** "Introduction to Symplectic Topology"

---

## Handoff Notes (for Next Agent)

**Summary:** This document specifies the mathematical foundations and Rust representations for computing the EHZ capacity of convex polytopes in ℝ⁴.

**Key Conventions:**

1. **Truth hierarchy:** Math papers → Thesis → Spec math → Spec Rust. Never justify conventions by Rust code; always trace back to the math source.

2. **Trivialization normal (CH2021):** Use the **exit facet's normal** (the facet we're entering). For a tube with `facet_sequence: [i, j, k, ...]`:
   - Start 2-face F_{i,j} is trivialized using exit_normal (per CH2021 Def 2.15)
   - TwoFaceEnriched fields are **flow-direction-aware**: entry_normal, exit_normal, and transition_matrix are computed based on actual flow direction, not the i < j convention
   - Callers can use these fields directly without checking flow_direction

3. **Facet sequence semantics:** `[i, j]` means "at 2-face F_{i,j}, entered facet j from facet i, about to flow along j."

4. **Rotation convention:** rot(init) = 0. Rotation is non-decreasing as one extends a trajectory. The algorithm uses ≥0 rotation increments.

5. **Near-singular handling:** Runtime error if numerics turn nearly singular (e.g., det ≈ 0 when solving for fixed points). Do not silently assume genericity.

6. **Testing strategy:** Don't rely solely on known capacity values. Use axioms (scaling, monotonicity, symplectic invariance), orbit validity tests, and internal invariants.

**Algorithm Domain:**

| Polytope Type | 2-Face Character | Applicable Algorithms |
|---------------|------------------|----------------------|
| Lagrangian products (K₁ × K₂) | ALL 2-faces Lagrangian | Billiard, HK2017 |
| Generic polytopes | SOME 2-faces Lagrangian | HK2017 only |
| Non-Lagrangian polytopes | NO 2-faces Lagrangian | Tube, HK2017 |

**Known Limitations:**
- No algorithm handles mixed Lagrangian/non-Lagrangian polytopes well
- HK2017 QP solver is incomplete (indefinite quadratic requires global optimizer)
- Pentagon × RotatedPentagon returns wrong value (known bug, under investigation)

**Related Files:**
- `review-spec-v2.md`: Detailed review with recommendations
- `mathematical-claims.md`: Citation tracking for all claims
- `test-propositions.md`: Mathematical propositions underlying tests

---

## 5. Implementation Guide

This section provides guidance for agents implementing the tube algorithm.

### 5.1 Scope

**Current implementation target:** Tube algorithm only (Section 3.4). Billiard and HK2017 algorithms are out of scope for now.

### 5.2 Crate Structure

Start simple:
- `packages/rust_viterbo/tube/` — Main implementation crate
- `packages/rust_viterbo/ffi/` — Python bindings (existing, to be updated)

Refactor into separate `geom` and `algorithm` crates later if needed.

### 5.3 Dependencies

- Use `nalgebra` for linear algebra (`Vector4<f64>`, `Matrix2<f64>`, etc.)
- Avoid magic type aliases; `Vector4<f64>` is clear and readable

### 5.4 Development Approach

**TDD with falsification mindset:**
1. Write tests that would CATCH bugs, not just confirm correctness
2. Actively seek weak points in code, tests, AND spec
3. If something seems wrong in the spec, escalate — don't silently work around it

**Move carefully:**
- This is complex work; don't try to implement everything at once
- Verify each component before building on it
- Use debug assertions liberally during development

**Correctness over performance:**
- Get it working correctly first
- Only optimize after profiling identifies actual bottlenecks

### 5.5 Escalation Boundaries

**Stop and escalate if:**
- Rust environment setup takes >10 minutes
- Unit test suite takes >3 minutes total
- You encounter unexpected behavior that doesn't resolve with minor adjustments
- You find what appears to be a spec error

### 5.6 Subagent Usage

Use `Task()` subagents for:
- Detailed coding work (stay focused on architecture)
- Debugging sessions
- Exploratory investigation

Run one subagent at a time to avoid conflicts.

### 5.7 Checkpoints

Suggested implementation order:
1. **Polytope data structures** — H-rep, validation, basic symplectic primitives
2. **2-face enumeration** — Find all 2-faces, classify Lagrangian vs non-Lagrangian
3. **Trivialization** — Implement and test τ, τ⁻¹, verify symplectic preservation
4. **Root tubes** — Initialize tubes at each 2-face
5. **Tube extension** — Flow map, action function, rotation accumulation
6. **Closure detection** — Identify next-step closeable and closed tubes
7. **Fixed point finding** — Solve ψ(s) = s for closed tubes
8. **4D reconstruction** — Convert 2D fixed points to 4D orbits, validate
9. **Branch-and-bound** — Full algorithm with pruning
10. **FFI bindings** — Expose to Python

### 5.8 Verification Markers

The following sections have been flagged for verification if bugs occur:
- **Flow map computation (§2.10):** Uses `exit_normal` from enriched 2-faces. If orbits don't close or fixed points are wrong, check this first.
- **Closed tube minimum length:** Claimed to be 5 (3 distinct facets). Verify the antisymmetry argument.
