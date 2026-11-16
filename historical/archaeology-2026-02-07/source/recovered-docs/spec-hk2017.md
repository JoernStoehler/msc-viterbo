# Developer Specification: HK2017 Crate

> **Audience:** Claude Code agents implementing the HK2017 algorithm
> **Prerequisite:** Read thesis chapter on algorithms; review HK2017 paper ([HK2017-EHZ-polytopes.tex](../../../docs/papers/HK2017-EHZ-polytopes/HK2017-EHZ-polytopes.tex))
> **Status:** Implemented and tested (both Naive and GraphPruned enumeration verified)
> **Reference Implementation:** [pazithaimkislev/EHZ-capacity](https://github.com/pazithaimkislev/EHZ-capacity) (MATLAB)

---

## Table of Contents

0. [Problem Statement](#0-problem-statement)
1. [Mathematical Background](#1-mathematical-background)
   - 1.1 The HK2017 Formula
   - 1.2 The Q-Function
   - 1.3 Constraint Set M(K)
   - 1.4 Simple Orbits Theorem
   - 1.5 Equivalent Formulations
2. [Data Structures](#2-data-structures)
   - 2.1 Polytope Input
   - 2.2 Facet Data
   - 2.3 Algorithm State
   - 2.4 Result
3. [Algorithm](#3-algorithm)
   - 3.1 Overview
   - 3.2 Preprocessing
   - 3.3 Permutation Enumeration (Naive)
   - 3.4 Constrained Optimization per Permutation
   - 3.5 Graph-Based Pruning (Optional)
4. [Implementation Notes](#4-implementation-notes)
   - 4.1 Linear Algebra Setup
   - 4.2 Solving the Constrained QP
   - 4.3 Numerical Tolerances
   - 4.4 Complexity Analysis
5. [Test Cases](#5-test-cases)
   - 5.1 Ground Truth Values
   - 5.2 Capacity Axioms
   - 5.3 Algorithm Agreement
6. [Crate Structure](#6-crate-structure)
7. [References](#7-references)

---

## 0. Problem Statement

### What We Compute

**Input:** A polytope \(K \subset \mathbb{R}^4\) with \(0 \in \mathrm{int}(K)\), given in H-representation.

**Output:** The Ekeland-Hofer-Zehnder capacity \(c_{\text{EHZ}}(K)\).

### Scope

This crate implements **capacity computation only**. It does not reconstruct the actual Reeb orbit achieving the minimum action. Orbit reconstruction is left to other algorithms (Tube, Billiard) or future work.

### Why HK2017?

The HK2017 algorithm:
- Works for **all polytopes** (Lagrangian products, non-Lagrangian, mixed)
- Provides a **combinatorial formula** that is exact (no numerical integration)
- Is the **reference algorithm** for verifying other algorithms

**Limitation:** Complexity is O(F!) where F = number of facets. Practical limit is ~10-12 facets.

---

## 1. Mathematical Background

### 1.1 The HK2017 Formula

**Source:** HK2017 Theorem 1.1 (Formula 1.1)

For a convex polytope \(K \subset \mathbb{R}^4\) with F facets:

\[
c_{\text{EHZ}}(K) = \frac{1}{2} \left[ \max_{\sigma \in S_F, \, \beta \in M(K)} Q(\sigma, \beta) \right]^{-1}
\]

where:
- \(S_F\) is the symmetric group on F elements (all permutations)
- \(M(K)\) is the constraint set (defined below)
- \(Q(\sigma, \beta)\) is the Q-function (defined below)

**Interpretation:** We search over all orderings of facets (permutations σ) and all valid coefficient vectors β to maximize a quadratic form Q. The capacity is the reciprocal of this maximum (times 1/2).

### 1.2 The Q-Function

**Definition:** For a permutation \(\sigma\) and coefficients \(\beta = (\beta_1, \ldots, \beta_F)\):

\[
Q(\sigma, \beta) = \sum_{1 \leq j < i \leq F} \beta_{\sigma(i)} \beta_{\sigma(j)} \omega(n_{\sigma(i)}, n_{\sigma(j)})
\]

where:
- \(n_i\) is the unit outward normal to facet \(F_i\)
- \(\omega(x, y) = \langle Jx, y \rangle\) is the standard symplectic form
- \(J\) is the standard complex structure: \(J(q_1, q_2, p_1, p_2) = (-p_1, -p_2, q_1, q_2)\)

**Key observation:** The Q-function depends on the **order** of facets (via σ), not just which facets participate. The symplectic form is antisymmetric: \(\omega(x,y) = -\omega(y,x)\), so the order in the sum matters.

```rust
/// Compute Q(σ, β) for a given permutation and coefficients
fn q_function(
    sigma: &[usize],           // permutation as array of facet indices
    beta: &[f64],              // coefficients β_i (same length as sigma)
    normals: &[Vector4<f64>],  // facet normals n_i
) -> f64 {
    let k = sigma.len();
    let mut q = 0.0;
    for i in 1..k {
        for j in 0..i {
            let ni = &normals[sigma[i]];
            let nj = &normals[sigma[j]];
            q += beta[sigma[i]] * beta[sigma[j]] * symplectic_form(ni, nj);
        }
    }
    q
}

fn symplectic_form(x: &Vector4<f64>, y: &Vector4<f64>) -> f64 {
    // ω(x,y) = q₁p₁' + q₂p₂' - p₁q₁' - p₂q₂' = ⟨Jx, y⟩
    let jx = Vector4::new(-x[2], -x[3], x[0], x[1]);
    jx.dot(y)
}
```

### 1.3 Constraint Set M(K)

**Definition:**

\[
M(K) = \left\{ (\beta_i)_{i=1}^{F} : \beta_i \geq 0, \quad \sum_{i=1}^{F} \beta_i h_i = 1, \quad \sum_{i=1}^{F} \beta_i n_i = 0 \right\}
\]

where \(h_i = h_K(n_i) = \max_{x \in K} \langle n_i, x \rangle\) is the support function value (= distance from origin to facet along normal direction).

**Interpretation:**
1. **Non-negativity:** \(\beta_i \geq 0\) (time spent on each facet is non-negative)
2. **Height normalization:** \(\sum \beta_i h_i = 1\) (trajectory "height sum" normalized)
3. **Closure constraint:** \(\sum \beta_i n_i = 0\) (trajectory closes, net displacement is zero)

**Geometry:** M(K) is a convex polytope in \(\mathbb{R}^F\) defined by F non-negativity constraints, 1 equality constraint (height), and 4 equality constraints (closure in \(\mathbb{R}^4\)). Its dimension is at most F - 5.

```rust
/// The constraint set M(K) as linear constraints
/// Variables: β = (β_0, ..., β_{F-1})
/// Constraints:
///   - β_i ≥ 0 for all i                    (F inequality constraints)
///   - Σ β_i h_i = 1                         (1 equality constraint)
///   - Σ β_i n_i = 0                         (4 equality constraints in R^4)
struct ConstraintSet {
    normals: Vec<Vector4<f64>>,  // n_i (unit outward normals)
    heights: Vec<f64>,           // h_i > 0 (since 0 ∈ int(K))
}

impl ConstraintSet {
    /// Build the equality constraint matrix A and vector b
    /// such that A * β = b
    /// Row 0: height constraint (Σ β_i h_i = 1)
    /// Rows 1-4: closure constraints (Σ β_i n_i = 0)
    fn equality_constraints(&self) -> (DMatrix<f64>, DVector<f64>) {
        let f = self.normals.len();
        let mut a = DMatrix::zeros(5, f);
        let mut b = DVector::zeros(5);

        // Height constraint
        for i in 0..f {
            a[(0, i)] = self.heights[i];
        }
        b[0] = 1.0;

        // Closure constraints (4 rows for R^4)
        for i in 0..f {
            for d in 0..4 {
                a[(1 + d, i)] = self.normals[i][d];
            }
        }
        // b[1..5] = 0 (already initialized)

        (a, b)
    }
}
```

### 1.4 Simple Orbits Theorem

**Source:** HK2017 Theorem 1.2

**Theorem:** For every convex polytope K, there exists a minimum-action closed Reeb orbit that is **simple**: it visits each facet at most once.

**Consequence:** When searching for the minimum, we only need to consider permutations where each facet appears at most once. Furthermore, facets with \(\beta_i = 0\) can be omitted from the permutation.

**Implication for algorithm:** We enumerate subsets of facets (not just full permutations), and for each subset, enumerate all orderings.

### 1.5 Equivalent Formulations

**Alternative 1 (Min-form):** HK2017 Remark 2.6

\[
c_{\text{EHZ}}(K) = \frac{1}{2} \min_{(\beta, n) \in M_2(K)} \left( \sum_{i=1}^{k} \beta_i h_K(n_i) \right)^2
\]

where \(M_2(K)\) requires \(Q = 1\) instead of height sum = 1.

**Alternative 2 (Reeb-vector form):** Using \(p_i = \frac{2}{h_i} J n_i\) (Reeb vectors):

\[
c_{\text{EHZ}}(K) = 2 \left[ \max_{\sigma, T} \sum_{j<i} T_{\sigma(i)} T_{\sigma(j)} \omega(p_{\sigma(i)}, p_{\sigma(j)}) \right]^{-1}
\]

where \(T_i \geq 0\), \(\sum T_i = 1\), \(\sum T_i p_i = 0\).

We use the original max-form (Section 1.1) as the primary implementation.

---

## 2. Data Structures

### 2.1 Polytope Input

```rust
use nalgebra::{Vector4, DMatrix, DVector};

/// H-representation of a polytope K = {x : ⟨n_i, x⟩ ≤ h_i for all i}
/// Requirement: 0 ∈ int(K), so h_i > 0 for all i
pub struct PolytopeHRep {
    pub normals: Vec<Vector4<f64>>,   // unit outward normals
    pub heights: Vec<f64>,            // h_i > 0 (distance from origin to facet)
}

// Mathematical conditions (not encoded in type):
// - normals[i].norm() == 1.0 (within tolerance)
// - heights[i] > 0 for all i (origin is in interior)
// - No redundant half-spaces (each facet contributes to the boundary)
// - Polytope is bounded (normals positively span R^4)
// - At least 2 facets (minimum for a closed orbit to exist)

impl PolytopeHRep {
    pub fn num_facets(&self) -> usize {
        self.normals.len()
    }

    pub fn validate(&self) -> Result<(), Hk2017Error> {
        // Check lengths match
        if self.normals.len() != self.heights.len() {
            return Err(Hk2017Error::InvalidPolytope(
                "normals and heights must have same length".to_string()));
        }

        // Need at least 2 facets for a valid closed orbit
        if self.normals.len() < 2 {
            return Err(Hk2017Error::InvalidPolytope(
                "need at least 2 facets".to_string()));
        }

        // Check normals are unit vectors
        for (i, n) in self.normals.iter().enumerate() {
            if (n.norm() - 1.0).abs() > EPS {
                return Err(Hk2017Error::InvalidPolytope(
                    format!("normal {} is not unit: norm = {}", i, n.norm())));
            }
        }

        // Check heights are positive (0 in interior)
        for (i, &h) in self.heights.iter().enumerate() {
            if h <= EPS {
                return Err(Hk2017Error::InvalidPolytope(
                    format!("height {} is not positive: h = {} (origin not in interior)", i, h)));
            }
        }

        Ok(())
    }
}

/// Error types for HK2017 algorithm
#[derive(Debug)]
pub enum Hk2017Error {
    InvalidPolytope(String),      // Input validation failed
    SingularKkt,                  // KKT system is singular
    NoPositiveQ,                  // All permutations give Q ≤ 0
    NumericalInstability(String), // Computation failed numerically
}
```

### 2.2 Facet Data

**Note on heights:** For H-representation K = {x : ⟨n_i, x⟩ ≤ d_i} with **unit** normals, the height h_i = d_i directly. If normals are stored unnormalized, then h_i = d_i / ||n_i||.

The algorithm precomputes data about facets:

```rust
/// Precomputed facet data for HK2017 algorithm
pub struct FacetData {
    pub num_facets: usize,
    pub normals: Vec<Vector4<f64>>,   // n_i
    pub heights: Vec<f64>,            // h_i
    pub reeb_vectors: Vec<Vector4<f64>>,  // p_i = (2/h_i) * J * n_i
    pub omega_matrix: DMatrix<f64>,   // ω[i,j] = ω(n_i, n_j)
}

impl FacetData {
    pub fn from_polytope(polytope: &PolytopeHRep) -> Self {
        let f = polytope.num_facets();
        let normals = polytope.normals.clone();
        let heights = polytope.heights.clone();

        // Compute Reeb vectors
        let reeb_vectors: Vec<Vector4<f64>> = (0..f)
            .map(|i| {
                let jn = j_matrix() * &normals[i];
                jn * (2.0 / heights[i])
            })
            .collect();

        // Precompute symplectic form matrix
        let mut omega_matrix = DMatrix::zeros(f, f);
        for i in 0..f {
            for j in 0..f {
                omega_matrix[(i, j)] = symplectic_form(&normals[i], &normals[j]);
            }
        }

        FacetData { num_facets: f, normals, heights, reeb_vectors, omega_matrix }
    }

    /// Validate precomputed data (useful for debugging)
    pub fn validate(&self) {
        // Reeb vectors are perpendicular to normals (Jn ⊥ n)
        for i in 0..self.num_facets {
            assert!(self.reeb_vectors[i].dot(&self.normals[i]).abs() < EPS,
                "Reeb vector {} not perpendicular to normal", i);
        }

        // Omega matrix is antisymmetric
        for i in 0..self.num_facets {
            for j in 0..self.num_facets {
                assert!((self.omega_matrix[(i, j)] + self.omega_matrix[(j, i)]).abs() < EPS,
                    "Omega matrix not antisymmetric at ({}, {})", i, j);
            }
        }

        // Diagonal of omega is zero
        for i in 0..self.num_facets {
            assert!(self.omega_matrix[(i, i)].abs() < EPS,
                "Omega diagonal not zero at {}", i);
        }
    }
}
```

### 2.3 Algorithm State

```rust
/// Configuration for HK2017 algorithm
pub struct Hk2017Config {
    /// Use graph-based pruning (reduces search space)
    pub use_adjacency_pruning: bool,

    /// Numerical tolerance for constraint satisfaction
    pub constraint_tol: f64,

    /// Numerical tolerance for positive definiteness checks
    pub positive_tol: f64,
}

impl Default for Hk2017Config {
    fn default() -> Self {
        Hk2017Config {
            use_adjacency_pruning: false,  // naive enumeration by default
            constraint_tol: 1e-10,
            positive_tol: 1e-10,
        }
    }
}
```

### 2.4 Result

```rust
/// Result of HK2017 capacity computation
pub struct Hk2017Result {
    /// The computed EHZ capacity
    pub capacity: f64,

    /// The optimal permutation (facet indices in order)
    pub optimal_permutation: Vec<usize>,

    /// The optimal β coefficients (indexed by facet)
    pub optimal_beta: Vec<f64>,

    /// The maximum Q value achieved (capacity = 1 / (2 * q_max))
    pub q_max: f64,

    /// Number of permutations evaluated
    pub permutations_evaluated: usize,

    /// Number of permutations pruned (if adjacency pruning enabled)
    pub permutations_pruned: usize,
}
```

---

## 3. Algorithm

### 3.1 Overview

```
Algorithm HK2017(K):
    Input: Polytope K in H-rep
    Output: c_EHZ(K)

    1. Precompute facet data (normals, heights, omega matrix)
    2. Initialize q_max = 0
    3. For each subset S ⊆ {0, ..., F-1} with |S| ≥ 2:
        For each permutation σ of S:
            a. Build constraints for this permutation
            b. Solve for β maximizing Q(σ, β) subject to constraints
            c. If Q(σ, β*) > q_max: update q_max
    4. Return capacity = 1 / (2 * q_max)
```

**Key insight:** For a fixed permutation σ, the constraints are linear in β and Q is quadratic in β. This is a Quadratic Program (QP) with equality and inequality constraints.

### 3.2 Preprocessing

```rust
pub fn preprocess(polytope: &PolytopeHRep) -> FacetData {
    polytope.validate().expect("Invalid polytope");
    FacetData::from_polytope(polytope)
}
```

### 3.3 Permutation Enumeration (Naive)

The naive approach enumerates all subsets and all permutations:

```rust
use itertools::Itertools;

/// Generate all permutations of subsets of size k from 0..n
fn subset_permutations(n: usize, k: usize) -> impl Iterator<Item = Vec<usize>> {
    (0..n).combinations(k).flat_map(|subset| subset.into_iter().permutations(k))
}

/// Enumerate all valid permutations (subsets of size 2 to F)
pub fn enumerate_permutations_naive(num_facets: usize) -> Vec<Vec<usize>> {
    let mut perms = Vec::new();
    for k in 2..=num_facets {
        for perm in subset_permutations(num_facets, k) {
            perms.push(perm);
        }
    }
    perms
}
```

**Complexity:** \(\sum_{k=2}^{F} \binom{F}{k} k! = \sum_{k=2}^{F} \frac{F!}{(F-k)!}\) which is O(F!).

### 3.4 Constrained Optimization per Permutation

> **⚠️ KNOWN LIMITATION: Boundary Maxima**
>
> The Hessian H of Q is symmetric but **indefinite** (has both positive and negative eigenvalues). This means:
> - The interior critical point (from KKT) may be a **saddle point**, not the maximum
> - The true maximum may be on the **boundary** of M(K) where some βᵢ = 0
> - The implementation below checks **only the interior critical point**
>
> This limitation is shared with the MATLAB reference implementation. For most test cases (tesseract, rectangles), the interior critical point happens to be the global maximum. **This is not guaranteed in general.**
>
> A complete implementation would enumerate all faces of M(K) using an active-set method: when the interior solution has βᵢ < 0, fix βᵢ = 0 and recurse on the lower-dimensional face.

For a fixed permutation σ = (σ₁, ..., σₖ), we solve:

\[
\max_{\beta \geq 0} Q(\sigma, \beta) \quad \text{s.t.} \quad \sum \beta_{\sigma(i)} h_{\sigma(i)} = 1, \quad \sum \beta_{\sigma(i)} n_{\sigma(i)} = 0
\]

**Approach 1: Lagrange Multipliers (MATLAB implementation approach)**

For the unconstrained critical point, use the KKT conditions. Build the system:

\[
\begin{pmatrix} 2H & A^T \\ A & 0 \end{pmatrix}
\begin{pmatrix} \beta \\ \lambda \end{pmatrix}
=
\begin{pmatrix} 0 \\ b \end{pmatrix}
\]

where H is the Hessian of Q (quadratic in β), A is the equality constraint matrix, b is the RHS.

If the solution has all βᵢ ≥ 0, it's valid. Otherwise, the maximum is on the boundary (some βᵢ = 0).

```rust
/// Solve the QP for a fixed permutation
/// Returns (Q_value, beta_vector) or None if infeasible
fn solve_for_permutation(
    sigma: &[usize],
    facet_data: &FacetData,
    config: &Hk2017Config,
) -> Option<(f64, Vec<f64>)> {
    let k = sigma.len();
    if k < 2 {
        return None;  // Need at least 2 facets
    }

    // Build Hessian H where H[i,j] = ω(n_σ(i), n_σ(j)) for i > j
    // Q(β) = Σ_{j<i} β_σ(i) β_σ(j) ω(n_σ(i), n_σ(j))
    // ∂Q/∂β_σ(i) = Σ_{j≠i} β_σ(j) ω_ordered(i,j)
    // where ω_ordered(i,j) = ω(n_σ(i), n_σ(j)) if i > j, else ω(n_σ(j), n_σ(i))

    // The Hessian of Q is NOT symmetric in general!
    // H[i,j] = ∂²Q/∂β_σ(i)∂β_σ(j) = ω_ordered(i,j)
    // We need to handle this carefully.

    // Actually, let's write Q more carefully:
    // Q = Σ_{j<i} β_σ(i) β_σ(j) ω(n_σ(i), n_σ(j))
    //   = (1/2) Σ_{i≠j} β_σ(i) β_σ(j) * sign(i-j) * ω(n_σ(i), n_σ(j))
    //   = (1/2) β^T H β  where H[i,j] = sign(i-j) * ω(n_σ(i), n_σ(j))
    //
    // But ω is antisymmetric, so ω(n_σ(i), n_σ(j)) = -ω(n_σ(j), n_σ(i))
    // Therefore H[i,j] = sign(i-j) * ω(n_σ(i), n_σ(j))
    //          H[j,i] = sign(j-i) * ω(n_σ(j), n_σ(i)) = -sign(i-j) * (-ω(n_σ(i), n_σ(j)))
    //                 = sign(i-j) * ω(n_σ(i), n_σ(j)) = H[i,j]
    // So H is actually symmetric!

    let mut h = DMatrix::zeros(k, k);
    for i in 0..k {
        for j in 0..i {
            let omega_ij = facet_data.omega_matrix[(sigma[i], sigma[j])];
            h[(i, j)] = omega_ij;
            h[(j, i)] = omega_ij;  // Symmetric because of sign(i-j) and antisymmetry of ω
        }
    }

    // Build equality constraints for the k participating facets
    // A_eq * β = b_eq
    // Row 0: Σ β_σ(i) h_σ(i) = 1
    // Rows 1-4: Σ β_σ(i) n_σ(i)[d] = 0
    let mut a_eq = DMatrix::zeros(5, k);
    let mut b_eq = DVector::zeros(5);

    for (local_i, &global_i) in sigma.iter().enumerate() {
        a_eq[(0, local_i)] = facet_data.heights[global_i];
        for d in 0..4 {
            a_eq[(1 + d, local_i)] = facet_data.normals[global_i][d];
        }
    }
    b_eq[0] = 1.0;

    // Solve using Lagrange multipliers
    // KKT system: [H   A^T] [β]   = [0]
    //             [A   0  ] [λ]     [b]
    // (For constrained max of Q = (1/2)β^T H β, gradient is Hβ)
    let n_vars = k;
    let n_constraints = 5;
    let system_size = n_vars + n_constraints;

    let mut kkt = DMatrix::zeros(system_size, system_size);
    let mut rhs = DVector::zeros(system_size);

    // Fill in H (top-left)
    for i in 0..k {
        for j in 0..k {
            kkt[(i, j)] = h[(i, j)];
        }
    }

    // Fill in A^T (top-right) and A (bottom-left)
    for c in 0..n_constraints {
        for v in 0..n_vars {
            kkt[(v, n_vars + c)] = a_eq[(c, v)];
            kkt[(n_vars + c, v)] = a_eq[(c, v)];
        }
    }

    // Fill in RHS
    for c in 0..n_constraints {
        rhs[n_vars + c] = b_eq[c];
    }

    // Solve the system
    let decomp = kkt.clone().lu();
    let solution = decomp.solve(&rhs)?;

    // Extract β
    let beta_local: Vec<f64> = (0..k).map(|i| solution[i]).collect();

    // Check feasibility: all β ≥ 0
    let all_positive = beta_local.iter().all(|&b| b >= -config.positive_tol);
    if !all_positive {
        // Maximum is on the boundary; would need to enumerate boundary faces
        // For now, return None (incomplete: misses boundary maxima)
        // TODO: Enumerate faces of the feasible polytope
        return None;
    }

    // Compute Q value
    let q_value = compute_q(&beta_local, &h);

    // Map back to global β indexing
    let mut beta_global = vec![0.0; facet_data.num_facets];
    for (local_i, &global_i) in sigma.iter().enumerate() {
        beta_global[global_i] = beta_local[local_i];
    }

    Some((q_value, beta_global))
}

fn compute_q(beta: &[f64], h: &DMatrix<f64>) -> f64 {
    let k = beta.len();
    let mut q = 0.0;
    for i in 0..k {
        for j in 0..i {
            q += beta[i] * beta[j] * h[(i, j)];
        }
    }
    q
}
```

**Important limitation:** The interior critical point may not be the maximum. The Q-function is indefinite, so the true maximum may be on the boundary of the feasible region (some βᵢ = 0). A complete implementation requires enumerating faces of M(K). This is a known limitation also noted in the existing developer-spec-v2.md.

### 3.5 Graph-Based Pruning (Optional)

**Source:** HK2017 Remark 3.11

> **Verification Status:** Both Naive and GraphPruned enumeration have been tested and produce
> identical capacity values on all test polytopes (simplex, tesseract, rectangles). The constraint
> verification fix (detecting infeasible permutations via residual check) was critical for achieving
> agreement. See `benchmark-hk2017` experiment FINDINGS.md for details.

Build an undirected graph G where:
- Vertices = facets {0, ..., F-1}
- Edge i -- j exists iff facets i and j share at least one vertex (geometric adjacency)

Then only enumerate **cycles** in G, not all permutations.

> **⚠️ Important:** The correct pruning condition is **geometric adjacency** (shared vertices),
> NOT Reeb flow transitions. The HK2017 paper's Remark 3.11 discusses physical orbits, but
> the mathematical enumeration of permutations should use geometric adjacency:
>
> - **Geometric adjacency:** Facets i and j share a vertex of the polytope
> - **Reeb flow:** The flow from facet i in direction pᵢ can reach facet j
>
> These are NOT equivalent. For the tesseract, the optimal permutation [0, 2, 5, 1, 4, 6]
> uses geometrically adjacent facets (orthogonal normals share edges), but there are
> NO direct Reeb flow transitions between consecutive facets (⟨pᵢ, nⱼ⟩ = 0 for all pairs).
>
> Using Reeb flow pruning incorrectly rejects valid permutations.

```rust
/// Build the facet adjacency graph based on shared vertices.
///
/// Two facets are adjacent (share a vertex) if there exists a point x such that:
/// - n_i · x = h_i (on facet i)
/// - n_j · x = h_j (on facet j)
/// - n_k · x ≤ h_k for all other k (inside the polytope)
fn build_adjacency_graph(facet_data: &FacetData) -> Vec<Vec<usize>> {
    let f = facet_data.num_facets;

    // Enumerate vertices and their incident facets
    let (vertices, incidence) = enumerate_vertices(facet_data);

    // Build adjacency: facets i and j are adjacent if they share a vertex
    let mut adjacency: Vec<Vec<usize>> = vec![Vec::new(); f];

    for vertex_facets in &incidence {
        // For each pair of facets incident to this vertex, they are adjacent
        for i in 0..vertex_facets.len() {
            for j in (i + 1)..vertex_facets.len() {
                let fi = vertex_facets[i];
                let fj = vertex_facets[j];

                if !adjacency[fi].contains(&fj) {
                    adjacency[fi].push(fj);
                }
                if !adjacency[fj].contains(&fi) {
                    adjacency[fj].push(fi);
                }
            }
        }
    }

    adjacency
}

/// Enumerate all vertices of the polytope.
/// A vertex is the intersection of exactly 4 hyperplanes (in R^4) that lies
/// inside all other half-spaces.
fn enumerate_vertices(facet_data: &FacetData) -> (Vec<Vector4<f64>>, Vec<Vec<usize>>) {
    let f = facet_data.num_facets;
    let mut vertices = Vec::new();
    let mut incidence = Vec::new();

    // Try all combinations of 4 facets
    for combo in (0..f).combinations(4) {
        // Solve the 4x4 system A * x = b
        let mut a = Matrix4::zeros();
        let mut b = Vector4::zeros();
        for (row, &facet_idx) in combo.iter().enumerate() {
            a.set_row(row, &facet_data.normals[facet_idx].transpose());
            b[row] = facet_data.heights[facet_idx];
        }

        if let Some(x) = a.lu().solve(&b) {
            // Check if x satisfies all other constraints
            let mut is_vertex = true;
            let mut incident_facets: Vec<usize> = combo.clone();

            for k in 0..f {
                let slack = facet_data.heights[k] - facet_data.normals[k].dot(&x);
                if slack < -1e-10 {
                    is_vertex = false;
                    break;
                }
                if slack.abs() < 1e-10 && !incident_facets.contains(&k) {
                    incident_facets.push(k);
                }
            }

            if is_vertex {
                incident_facets.sort();
                vertices.push(x);
                incidence.push(incident_facets);
            }
        }
    }

    (vertices, incidence)
}

/// Enumerate all simple cycles in the adjacency graph
fn enumerate_cycles(adjacency: &[Vec<usize>], max_length: usize) -> Vec<Vec<usize>> {
    // ... (DFS cycle enumeration, same as before)
}
```

**Example: Tesseract [-1,1]⁴**

| Property | Value |
|----------|-------|
| Vertices | 16 (corners of 4-cube) |
| Facets | 8 (pairs of opposite hyperplanes) |
| Adjacent pairs | 24 (each facet adjacent to 6 others) |
| Non-adjacent pairs | 4 (opposite facet pairs: 0-1, 2-3, 4-5, 6-7) |
| Naive permutations | 109,592 |
| Graph-pruned cycles | 5,556 |

For axis-aligned boxes, two facets are adjacent iff their normals are orthogonal (not parallel).

---

## 4. Implementation Notes

### 4.1 Linear Algebra Setup

Use `nalgebra` consistently:

```rust
use nalgebra::{Vector4, Matrix4, DMatrix, DVector};

/// Standard complex structure J: (q₁,q₂,p₁,p₂) → (-p₁,-p₂,q₁,q₂)
fn j_matrix() -> Matrix4<f64> {
    Matrix4::new(
        0.0,  0.0, -1.0,  0.0,
        0.0,  0.0,  0.0, -1.0,
        1.0,  0.0,  0.0,  0.0,
        0.0,  1.0,  0.0,  0.0,
    )
}

fn symplectic_form(x: &Vector4<f64>, y: &Vector4<f64>) -> f64 {
    (j_matrix() * x).dot(y)
}
```

### 4.2 Solving the Constrained QP

The MATLAB implementation uses:
1. Build KKT system with Lagrange multipliers
2. Solve via LU decomposition
3. Check if solution is in feasible region (all β ≥ 0)

**Known issue:** When the interior critical point has some βᵢ < 0, the true maximum is on the boundary. The MATLAB code (and our basic implementation) doesn't enumerate boundary faces, so it may miss the true maximum. This is documented as a known limitation.

**Potential improvement:** Use a proper QP solver (e.g., OSQP, qpOASES) that handles inequality constraints.

### 4.3 Numerical Tolerances

```rust
/// Tolerance for checking constraint satisfaction
const CONSTRAINT_TOL: f64 = 1e-10;

/// Tolerance for checking β ≥ 0
const POSITIVE_TOL: f64 = 1e-10;

/// Tolerance for checking if two floats are equal
const EPS: f64 = 1e-12;

/// Tolerance for checking if omega is zero (Lagrangian face)
const EPS_LAGRANGIAN: f64 = 1e-8;
```

### 4.4 Complexity Analysis

| Component | Naive | With Graph Pruning |
|-----------|-------|-------------------|
| Permutations | O(F!) | O(|cycles in G|) |
| QP solve per permutation | O(k³) | O(k³) |
| Total | O(F! · F³) | O(|cycles| · F³) |

**Estimated running times (single thread, naive enumeration):**

| Facets | Ordered Subsets | Estimated Time | Example Polytope |
|--------|-----------------|----------------|------------------|
| 4      | 60              | < 1 ms         | 4-simplex |
| 6      | 1,956           | ~10 ms         | 3-cube (6 facets) |
| 8      | 109,600         | ~100 ms        | Tesseract |
| 10     | 9,864,100       | ~10 s          | Pentagon × Pentagon |
| 12     | 1.3 × 10⁹       | ~30 min        | - |
| 14     | 2.3 × 10¹¹      | ~days          | - |

**Notes:**
- With graph pruning, times can be 10-100× faster depending on polytope structure
- Parallelization is embarrassingly parallel (use `rayon::par_iter()`)
- Memory usage is dominated by storing permutations; consider iterator-based enumeration

---

## 5. Test Cases

### 5.1 Ground Truth Values

| Polytope | c_EHZ | Source | Notes |
|----------|-------|--------|-------|
| Tesseract [-1,1]⁴ | 4.0 | HK2017 Ex 4.6 | 8 facets, Lagrangian product |
| Simplex conv{0,e₁,e₂,e₃,e₄} | 0.25 | Y. Nir 2013 | 5 facets, **origin on boundary** (invalid input) |
| Rectangle 2×1 × Rectangle 2×1 | 1.0 | Scaling | 8 facets, Lagrangian product |
| Pentagon × RotatedPentagon | ≈3.441 | HK-O 2024 | 10 facets, counterexample |

**Note:** The simplex with vertex at origin is invalid (0 not in interior). Use translated simplex instead.

```rust
#[test]
fn test_tesseract() {
    // Tesseract [-1,1]^4: 8 facets with normals ±e_i
    let normals = vec![
        Vector4::new( 1.0,  0.0,  0.0,  0.0),
        Vector4::new(-1.0,  0.0,  0.0,  0.0),
        Vector4::new( 0.0,  1.0,  0.0,  0.0),
        Vector4::new( 0.0, -1.0,  0.0,  0.0),
        Vector4::new( 0.0,  0.0,  1.0,  0.0),
        Vector4::new( 0.0,  0.0, -1.0,  0.0),
        Vector4::new( 0.0,  0.0,  0.0,  1.0),
        Vector4::new( 0.0,  0.0,  0.0, -1.0),
    ];
    let heights = vec![1.0; 8];

    let polytope = PolytopeHRep { normals, heights };
    let result = hk2017_capacity(&polytope, &Hk2017Config::default());

    assert!((result.capacity - 4.0).abs() < 1e-6);
}
```

### 5.2 Capacity Axioms

```rust
#[test]
fn test_scaling_axiom() {
    // c(λK) = λ² c(K)
    let k = some_polytope();
    let lambda = 2.0;
    let k_scaled = scale_polytope(&k, lambda);

    let c_k = hk2017_capacity(&k, &default_config()).capacity;
    let c_scaled = hk2017_capacity(&k_scaled, &default_config()).capacity;

    assert!((c_scaled - lambda * lambda * c_k).abs() < 1e-6);
}

#[test]
fn test_translation_invariance() {
    // c(K + v) = c(K)
    let k = some_polytope();
    let v = Vector4::new(1.0, 2.0, 3.0, 4.0);
    let k_translated = translate_polytope(&k, &v);

    let c_k = hk2017_capacity(&k, &default_config()).capacity;
    let c_translated = hk2017_capacity(&k_translated, &default_config()).capacity;

    assert!((c_translated - c_k).abs() < 1e-6);
}
```

### 5.3 Algorithm Agreement

When other algorithms are available, verify agreement:

```rust
#[test]
fn test_hk2017_vs_billiard() {
    // For Lagrangian products, both should agree
    let k = lagrangian_product_polytope();

    let c_hk = hk2017_capacity(&k, &default_config()).capacity;
    let c_billiard = billiard_capacity(&k).capacity;

    assert!((c_hk - c_billiard).abs() < 1e-6);
}
```

### 5.4 Result Verification

Verify that the computed result satisfies all constraints:

```rust
/// Verify the capacity result by checking constraints and formula
fn verify_result(result: &Hk2017Result, facet_data: &FacetData) -> Result<(), String> {
    let sigma = &result.optimal_permutation;
    let beta = &result.optimal_beta;

    // 1. Check non-negativity: β_i ≥ 0
    for (i, &b) in beta.iter().enumerate() {
        if b < -POSITIVE_TOL {
            return Err(format!("β[{}] = {} is negative", i, b));
        }
    }

    // 2. Check height constraint: Σ β_i h_i = 1
    let height_sum: f64 = beta.iter().zip(&facet_data.heights)
        .map(|(&b, &h)| b * h).sum();
    if (height_sum - 1.0).abs() > CONSTRAINT_TOL {
        return Err(format!("Height sum = {} ≠ 1", height_sum));
    }

    // 3. Check closure constraint: Σ β_i n_i = 0
    let mut closure = Vector4::zeros();
    for (i, (&b, n)) in beta.iter().zip(&facet_data.normals).enumerate() {
        closure += n * b;
    }
    if closure.norm() > CONSTRAINT_TOL {
        return Err(format!("Closure norm = {} ≠ 0", closure.norm()));
    }

    // 4. Recompute Q value and check
    let q_computed = compute_q_for_permutation(sigma, beta, &facet_data.omega_matrix);
    if (q_computed - result.q_max).abs() > EPS {
        return Err(format!("Q mismatch: computed {} vs stored {}", q_computed, result.q_max));
    }

    // 5. Check capacity formula: c = 1/(2Q)
    if result.q_max <= 0.0 {
        return Err(format!("Q = {} is not positive", result.q_max));
    }
    let capacity_computed = 1.0 / (2.0 * result.q_max);
    if (capacity_computed - result.capacity).abs() > EPS {
        return Err(format!("Capacity mismatch: {} vs {}", capacity_computed, result.capacity));
    }

    Ok(())
}

fn compute_q_for_permutation(
    sigma: &[usize],
    beta: &[f64],
    omega_matrix: &DMatrix<f64>,
) -> f64 {
    let mut q = 0.0;
    for (pos_i, &facet_i) in sigma.iter().enumerate() {
        for (pos_j, &facet_j) in sigma.iter().enumerate().take(pos_i) {
            q += beta[facet_i] * beta[facet_j] * omega_matrix[(facet_i, facet_j)];
        }
    }
    q
}
```

---

## 6. Crate Structure

```
packages/rust_viterbo/hk2017/
├── Cargo.toml
├── src/
│   ├── lib.rs           # Public API
│   ├── types.rs         # Data structures
│   ├── preprocess.rs    # Polytope preprocessing
│   ├── enumerate.rs     # Permutation enumeration (naive + graph)
│   ├── solve.rs         # QP solver for fixed permutation
│   └── algorithm.rs     # Main algorithm orchestration
└── tests/
    ├── ground_truth.rs  # Known capacity values
    ├── axioms.rs        # Capacity axioms
    └── agreement.rs     # Algorithm agreement tests
```

**Cargo.toml:**

```toml
[package]
name = "hk2017"
version = "0.1.0"
edition = "2021"

[dependencies]
nalgebra = "0.32"
itertools = "0.12"

[dev-dependencies]
approx = "0.5"
```

**Public API (lib.rs):**

```rust
pub mod types;
pub mod preprocess;
pub mod enumerate;
pub mod solve;
pub mod algorithm;

pub use types::{PolytopeHRep, Hk2017Config, Hk2017Result};
pub use algorithm::hk2017_capacity;
```

---

## 7. References

### Primary Source

- **HK2017:** Haim-Kislev, P. "On the Symplectic Size of Convex Polytopes." *Geometric and Functional Analysis* 29 (2019): 440-463. arXiv:1712.03494 (December 2017).

### Reference Implementation

- **GitHub:** [pazithaimkislev/EHZ-capacity](https://github.com/pazithaimkislev/EHZ-capacity) (MATLAB, R2021b)

### Related

- **HK-O 2024:** Haim-Kislev & Ostrover, "A Counterexample to Viterbo's Conjecture." arXiv:2405.16513.
- **Y. Nir 2013:** "On Closed Characteristics and Billiards in Convex Bodies." Thesis, Tel Aviv University.

---

## Appendix A: Derivation of the Symmetric Hessian

The Q-function is:
\[
Q(\sigma, \beta) = \sum_{1 \leq j < i \leq k} \beta_{\sigma(i)} \beta_{\sigma(j)} \omega(n_{\sigma(i)}, n_{\sigma(j)})
\]

Rewriting with the Hessian:
\[
Q = \sum_{j < i} \beta_{\sigma(i)} \beta_{\sigma(j)} \omega_{ij}
\]

where \(\omega_{ij} = \omega(n_{\sigma(i)}, n_{\sigma(j)})\).

The gradient:
\[
\frac{\partial Q}{\partial \beta_{\sigma(l)}} = \sum_{j < l} \beta_{\sigma(j)} \omega_{lj} + \sum_{i > l} \beta_{\sigma(i)} \omega_{il}
\]

The Hessian:
\[
\frac{\partial^2 Q}{\partial \beta_{\sigma(l)} \partial \beta_{\sigma(m)}} =
\begin{cases}
\omega_{lm} & \text{if } l > m \\
\omega_{ml} & \text{if } m > l \\
0 & \text{if } l = m
\end{cases}
\]

Since \(\omega\) is antisymmetric (\(\omega_{ml} = -\omega_{lm}\)), we have:
\[
H_{lm} = \text{sign}(l - m) \cdot \omega(n_{\sigma(\max(l,m))}, n_{\sigma(\min(l,m))})
\]

This gives \(H_{lm} = H_{ml}\), so H is symmetric despite \(\omega\) being antisymmetric.

---

## Appendix B: Why the Maximum May Be on the Boundary

The Hessian H of Q is symmetric but **indefinite** (has both positive and negative eigenvalues) because the symplectic form has mixed signs.

For an indefinite quadratic form on a convex polytope:
- The interior critical point (from KKT) may be a saddle point
- The maximum over the polytope occurs at a vertex or on a face

**Example:** For 2 facets with \(\omega_{12} > 0\):
- H = [[0, ω], [ω, 0]] has eigenvalues ±ω
- Critical point at interior may be a saddle
- Maximum is at a vertex (extreme β values)

The MATLAB reference implementation checks only interior critical points, accepting this limitation. A complete implementation would enumerate all faces of M(K).
