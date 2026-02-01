# geom — Polytope Primitives and Shared Foundations

**Status:** Implementation complete

## Purpose

Shared geometric primitives for EHZ capacity algorithms. This crate provides:
- Polytope representation (H-rep)
- Volume computation via Qhull
- Systolic ratio calculation
- 2D geometry utilities (polygon operations, affine maps)
- Numerical tolerances

All capacity algorithms (HK2017, Tube, Billiard) depend on this crate.

---

## Spec Dependencies

> **IMPORTANT FOR AGENTS:** This spec defines shared mathematical concepts that are:
> - **Used by tube/SPEC.md and hk2017/SPEC.md** as foundational definitions
> - **Not necessarily implemented in geom code** — some are conceptual foundations
> - **Must not be pruned** even if not referenced in geom source files
>
> The dependency graph is:
> ```
> geom/SPEC.md (shared foundations)
>    ├── hk2017/SPEC.md (depends on: 2-faces, Lagrangian, orbits)
>    ├── tube/SPEC.md (depends on: 2-faces, flow direction, orbits)
>    └── billiard/SPEC.md (depends on: Lagrangian products)
> ```

**Shared concepts defined here:**
- 2-faces and adjacency (used by tube, hk2017)
- Lagrangian classification (used by all)
- Flow direction (used by tube)
- Reeb trajectories and orbits (used by all)
- Action formulas (used by all)

**Algorithm-specific concepts defined in crate specs:**
- Trivialization, transition matrices, rotation numbers → tube/SPEC.md
- Q-function, KKT constraints → hk2017/SPEC.md
- Minkowski billiards → billiard/SPEC.md

---

## Problem Statement

**Input:** A polytope K ⊂ ℝ⁴ with 0 ∈ int(K).

**Output:** The Ekeland-Hofer-Zehnder capacity c_EHZ(K) and a minimum-action closed Reeb orbit achieving it.

**The EHZ capacity:**
```
c_EHZ(K) = min { A(γ) : γ is a closed Reeb orbit on ∂K }
```

**Capacity axioms (what tests should verify):**
1. **Scaling:** c(λK) = λ² · c(K) for λ > 0
2. **Monotonicity:** K ⊆ L ⟹ c(K) ≤ c(L)
3. **Symplectic invariance:** c(AK + b) = c(K) for A ∈ Sp(4) and b ∈ ℝ⁴
4. **Normalization:** c(B⁴) = c(Z⁴) = π (ball and cylinder)

---

## Polytope Representation

### H-representation

A polytope is represented as the intersection of half-spaces:
```
K = ⋂ᵢ { x : ⟨nᵢ, x⟩ ≤ hᵢ }
```

```rust
pub struct PolytopeHRep {
    pub normals: Vec<Vector4<f64>>,  // unit outward normals
    pub heights: Vec<f64>,           // hᵢ > 0 (since 0 ∈ int(K))
}
```

**Code:** `polytope.rs`

**Validation:**
```rust
impl PolytopeHRep {
    pub fn validate(&self) -> Result<(), ValidationError> {
        // 1. Lengths match
        // 2. Normals are unit vectors
        // 3. Heights are positive (0 in interior)
        // 4. At least 5 facets (minimum for 4D polytope)
    }
}
```

### Facets (3-faces)

A **facet** Fᵢ is the intersection of K with the i-th bounding hyperplane:
```
Fᵢ = K ∩ { x : ⟨nᵢ, x⟩ = hᵢ }
```

Facets are 3-dimensional convex polytopes. Each facet has ≥4 vertices.

### Scaling

```rust
impl PolytopeHRep {
    /// Scale polytope by factor λ: K → λK
    /// Heights scale linearly: h'ᵢ = λ · hᵢ
    pub fn scale(&self, lambda: f64) -> Self;
}
```

---

## Volume Computation

Compute 4D polytope volume using Qhull's Delaunay triangulation.

```rust
pub fn polytope_volume_hrep(hrep: &PolytopeHRep) -> Result<f64, VolumeError>;
```

**Mathematical formula:** For a 4-simplex with vertices v₀, v₁, v₂, v₃, v₄:
```
Volume = (1/24) · |det([v₁-v₀, v₂-v₀, v₃-v₀, v₄-v₀])|
```

**Code:** `volume.rs`

---

## Systolic Ratio

The systolic ratio measures how "efficient" a polytope is:
```
sys(K) = c_EHZ(K)² / (2 · Vol(K))
```

Viterbo's conjecture (disproven 2024): sys(K) ≤ 1 for all convex K.
The HK-O 2024 counterexample has sys ≈ 1.047.

```rust
pub fn systolic_ratio(capacity: f64, volume: f64) -> f64;
```

**Code:** `systolic.rs`

---

## Symplectic Structure

### Symplectic Form

The standard symplectic form on ℝ⁴:
```
ω(x, y) = ⟨Jx, y⟩ = q₁p₁' + q₂p₂' - p₁q₁' - p₂q₂'
```

where J is the standard complex structure:
```
J(q₁, q₂, p₁, p₂) = (-p₁, -p₂, q₁, q₂)
```

**Properties:**
- Antisymmetric: ω(x, y) = -ω(y, x)
- Non-degenerate: ω(x, y) = 0 for all y implies x = 0

**Standard basis pairings:**
- ω(e₁, e₃) = 1, ω(e₂, e₄) = 1
- ω(e₁, e₂) = 0, ω(e₃, e₄) = 0 (Lagrangian pairs)

### Reeb Vectors

The Reeb vector on facet Fᵢ with normal nᵢ and height hᵢ:
```
Rᵢ = (2/hᵢ) · J · nᵢ
```

**Derivation:** For the contact form α = λ|_{∂K} where λ = ½(p dq - q dp), the Reeb vector R satisfies α(R) = 1 and ι_R dα = 0. At a point x on facet Fᵢ, this gives R(x) = (2/⟨x,nᵢ⟩) J nᵢ. Since ⟨x, nᵢ⟩ = hᵢ on the facet, we get Rᵢ = (2/hᵢ) J nᵢ.

**Properties:**
- Perpendicular to facet: ⟨Rᵢ, nᵢ⟩ = 0
- Magnitude: ‖Rᵢ‖ = 2/hᵢ

---

## Two-Faces and Adjacency

### Definition

A **2-face** F_{ij} is the intersection of two facets:
```
F_{ij} = Fᵢ ∩ Fⱼ = K ∩ { x : ⟨nᵢ, x⟩ = hᵢ } ∩ { x : ⟨nⱼ, x⟩ = hⱼ }
```

Two facets are **adjacent** iff their 2-face is nonempty and 2-dimensional (has ≥3 vertices).

```rust
struct TwoFace {
    i: usize,              // first facet index (i < j by convention)
    j: usize,              // second facet index
    vertices: Vec<usize>,  // indices of vertices on this 2-face
    omega_ij: f64,         // symplectic form: ω(nᵢ, nⱼ)
}
```

### Lagrangian vs Non-Lagrangian 2-Faces

A 2-face F_{ij} is **Lagrangian** iff ω(nᵢ, nⱼ) = 0.

```rust
impl TwoFace {
    fn is_lagrangian(&self) -> bool {
        self.omega_ij.abs() < EPS_LAGRANGIAN
    }
}
```

**Significance for algorithms:**
- **Tube algorithm:** Requires ALL 2-faces non-Lagrangian
- **HK2017:** Works on all polytopes
- **Billiard:** Requires Lagrangian product structure (all 2-faces Lagrangian)

### Flow Direction on Non-Lagrangian 2-Faces

For a non-Lagrangian 2-face F_{ij}, the Reeb flow crosses from one facet to the other:

- If ω(nᵢ, nⱼ) > 0: flow crosses from Fᵢ to Fⱼ
- If ω(nᵢ, nⱼ) < 0: flow crosses from Fⱼ to Fᵢ

**Proof:** The Reeb vector on Fᵢ is Rᵢ ∝ J nᵢ. Its inner product with nⱼ is ⟨J nᵢ, nⱼ⟩ = ω(nᵢ, nⱼ). When ω > 0, Rᵢ points outward from Fᵢ toward Fⱼ.

```rust
enum FlowDirection {
    ItoJ,  // ω(nᵢ, nⱼ) > 0
    JtoI,  // ω(nᵢ, nⱼ) < 0
}

impl TwoFace {
    fn flow_direction(&self) -> Option<FlowDirection> {
        if self.is_lagrangian() {
            None  // no crossing
        } else if self.omega_ij > 0.0 {
            Some(FlowDirection::ItoJ)
        } else {
            Some(FlowDirection::JtoI)
        }
    }
}
```

---

## Support Function and Polar Body

### Support Function

The **support function** of a convex body K:
```
h_K(d) = max_{x ∈ K} ⟨d, x⟩
```

For a polytope with known vertices:
```rust
fn support_function(vertices: &[Vector4<f64>], direction: &Vector4<f64>) -> f64 {
    vertices.iter().map(|v| direction.dot(v)).fold(f64::NEG_INFINITY, f64::max)
}
```

### Polar Body

The **polar body** (dual) of K:
```
K° = { y ∈ ℝ⁴ : ⟨x, y⟩ ≤ 1 for all x ∈ K }
```

For a 2D polygon in H-rep {x : ⟨nᵢ, x⟩ ≤ hᵢ}, the polar has vertices at nᵢ/hᵢ:
```rust
fn polar_vertices_2d(normals: &[Vector2<f64>], heights: &[f64]) -> Vec<Vector2<f64>> {
    normals.iter().zip(heights).map(|(n, &h)| n / h).collect()
}
```

**Use in Billiard algorithm:** The "T-length" of a Minkowski billiard trajectory is measured using K₂° as the unit ball.

---

## Lagrangian Product Structure

A polytope K is a **Lagrangian product** iff K = K₁ × K₂ where:
- K₁ ⊂ ℝ²_q (configuration space, coordinates q₁, q₂)
- K₂ ⊂ ℝ²_p (momentum space, coordinates p₁, p₂)

**Detection:** Every facet normal has either only q-coordinates or only p-coordinates nonzero:

```rust
fn is_lagrangian_product(hrep: &PolytopeHRep) -> bool {
    hrep.normals.iter().all(|n| {
        let q_part = n[0].abs() + n[1].abs();
        let p_part = n[2].abs() + n[3].abs();
        (q_part < EPS) || (p_part < EPS)
    })
}
```

**Significance:** The product structure K_q × K_p enables the specialized Billiard algorithm, which exploits that Reeb orbits decompose into independent q and p components.

---

## Closed Curves and Action

### Action of Closed Curves

A closed curve γ: [0,T] → ℝ⁴ with γ(0) = γ(T) has action:
```
A(γ) = ½ ∫₀ᵀ ⟨Jγ(t), γ̇(t)⟩ dt = ∮_γ λ
```

where λ = ½(p dq - q dp) is the Liouville 1-form.

### Action of Piecewise Linear Curves

For a closed polygonal curve with vertices v₀, v₁, ..., v_{n-1}, v_n = v₀:
```
A = ½ Σₖ ω(vₖ, vₖ₊₁)
```

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

**Properties:**
- Cyclic invariant: rotating the starting vertex doesn't change action
- Orientation: reversing orientation negates action

---

## Reeb Trajectories

### Definition

A **Reeb trajectory** is a curve γ: [0,T] → ∂K satisfying the Reeb flow differential inclusion:
```
γ̇(t) ∈ cone{ Rᵢ : γ(t) ∈ Fᵢ }
```

At a point on a single facet, velocity = Reeb vector. At a point on multiple facets (2-face, edge, vertex), velocity is a non-negative combination of the active Reeb vectors.

### Piecewise Linear Reeb Trajectories

On polytopes, Reeb trajectories are piecewise linear:

```rust
struct PiecewiseLinearReebTrajectory {
    breakpoints: Vec<Vector4<f64>>,  // p₀, p₁, ..., pₘ
    segment_facets: Vec<usize>,      // which facet for each segment
    segment_times: Vec<f64>,         // duration of each segment
}
```

**Conditions:**
1. Each breakpoint lies on ∂K
2. Each segment lies on its claimed facet
3. Velocity = Reeb vector: (pₖ₊₁ - pₖ) / τₖ = Rᵢ
4. Times positive: τₖ > 0

### Action = Period for Reeb Flow

For Reeb dynamics, **action equals period**:
```
A(γ) = T = Σₖ τₖ
```

**Proof:** The Reeb vector R is defined by α(R) = 1. For a Reeb orbit parametrized by t ∈ [0,T]:
```
A(γ) = ∫_γ α = ∫₀ᵀ α(γ̇(t)) dt = ∫₀ᵀ α(R) dt = ∫₀ᵀ 1 dt = T
```

---

## Closed Reeb Orbits

A **closed Reeb orbit** is a Reeb trajectory with γ(T) = γ(0).

```rust
struct ClosedReebOrbit {
    period: f64,                     // T = action
    breakpoints: Vec<Vector4<f64>>,  // p₀, ..., pₘ with pₘ = p₀
    segment_facets: Vec<usize>,      // i₀, ..., i_{m-1}
    segment_times: Vec<f64>,         // τ₀, ..., τ_{m-1}
}
```

**Conditions:**
- Closure: breakpoints[m] = breakpoints[0]
- Period = Σ segment_times
- Period = action (from general formula)

### Simple Reeb Orbits

A **simple Reeb orbit** visits each facet at most once.

**Source:** HK2017 Theorem 2 proves that minimum-action orbits are simple.

**Consequence:** All algorithms only need to search over simple orbits.

### Orbit Validity Checks

Comprehensive validation for computed orbits:

```rust
impl ClosedReebOrbit {
    fn validate(&self, hrep: &PolytopeHRep) -> Result<(), ValidationError> {
        // 1. Closure: last breakpoint = first breakpoint
        // 2. Breakpoints on boundary: each pₖ satisfies ⟨nᵢ, pₖ⟩ = hᵢ for some i
        // 3. Segments on facets: both endpoints of segment k satisfy facet equation
        // 4. Velocities match Reeb: (pₖ₊₁ - pₖ)/τₖ = Rᵢ = (2/hᵢ)Jnᵢ
        // 5. Period consistency: period = Σ τₖ = action(orbit)
    }
}
```

**Validation conditions:**

| # | Check | Formula |
|---|-------|---------|
| 1 | Closure | ‖pₘ - p₀‖ < ε |
| 2 | On boundary | ∃i: ⟨nᵢ, pₖ⟩ = hᵢ |
| 3 | On facet | ⟨nᵢ, pₖ⟩ = hᵢ and ⟨nᵢ, pₖ₊₁⟩ = hᵢ |
| 4 | Velocity | ‖(pₖ₊₁ - pₖ)/τₖ - Rᵢ‖ < ε‖Rᵢ‖ |
| 5 | Period | \|T - Σₖ τₖ\| < ε and \|T - A(γ)\| < εT |

---

## Facet Sequences

A **facet sequence** σ = (i₀, i₁, ..., iₘ) describes the order of facets visited by an orbit.

For orbits not involving Lagrangian 2-faces:
1. Each consecutive pair (iₖ, iₖ₊₁) must share a non-Lagrangian 2-face
2. Flow direction must be consistent with ω(nᵢ, nⱼ)

**Minimum closed sequence length is 5:**

A closed orbit requires at least 3 distinct facets, giving minimum sequence [i₀, i₁, i₂, i₀, i₁].

*Proof:* Length 4 [i, j, i, j] would require flow i→j then j→i at the same 2-face. But flow direction is fixed by ω(nᵢ, nⱼ). By antisymmetry, flow cannot reverse. □

---

## 2D Geometry Utilities

These utilities operate on 2D polygons and affine maps, used when working with trivialized 2-face tangent spaces.

### Polygon2D

```rust
struct Polygon2D {
    vertices: Vec<Vector2<f64>>,  // CCW-ordered vertices
}
```

### CCW Sorting

Sort 2D points in counter-clockwise order around their centroid:

```rust
fn sort_ccw(points: Vec<Vector2<f64>>) -> Vec<Vector2<f64>> {
    // Compute centroid, sort by angle from centroid
}
```

**Precondition:** Points form a convex polygon.

### Polygon Intersection (Sutherland-Hodgman)

Compute intersection of two convex polygons:

```rust
fn intersect_polygons(p1: &Polygon2D, p2: &Polygon2D) -> Polygon2D {
    // Clip p1 against each edge of p2
}
```

**Reference:** O'Rourke, "Computational Geometry in C", Chapter 7.

**Subroutines:**
- `clip_polygon_by_halfplane`: Keep points on the left side of a directed edge
- `is_left_of_edge`: Cross product sign test
- `line_intersection`: Standard line-line intersection

### Point-in-Polygon

Test if a point is inside a convex polygon (CCW vertices):

```rust
fn point_in_polygon(p: &Vector2<f64>, polygon: &Polygon2D) -> bool {
    // For convex polygons: inside iff left of all edges
}
```

### Polygon Area

Shoelace formula for polygon area:

```rust
fn polygon_area(p: &Polygon2D) -> f64 {
    // ½ |Σᵢ (xᵢyᵢ₊₁ - xᵢ₊₁yᵢ)|
}
```

### Affine Maps

2D affine transformations x ↦ Ax + b:

```rust
struct AffineMap2D {
    matrix: Matrix2<f64>,
    offset: Vector2<f64>,
}

impl AffineMap2D {
    fn identity() -> Self;
    fn apply(&self, x: &Vector2<f64>) -> Vector2<f64>;
}

/// Compose f ∘ g: (Ax + b) ∘ (Cx + d) = (AC)x + (Ad + b)
fn compose_affine(f: &AffineMap2D, g: &AffineMap2D) -> AffineMap2D;
```

### Affine Functions

Scalar-valued affine functions f(x) = g·x + c:

```rust
struct AffineFunc {
    gradient: Vector2<f64>,
    constant: f64,
}

impl AffineFunc {
    fn eval(&self, x: &Vector2<f64>) -> f64;
}

/// Compose affine function with affine map: f(Ax + b)
/// Result: (Aᵀg)·x + (g·b + c)
fn compose_with_map(f: &AffineFunc, map: &AffineMap2D) -> AffineFunc;
```

---

## Tolerances

```rust
pub const EPS: f64 = 1e-10;           // General tolerance
pub const EPS_UNIT: f64 = 1e-9;       // Unit normal validation
pub const EPS_LAGRANGIAN: f64 = 1e-9; // Lagrangian detection
```

**Code:** `tolerances.rs`

---

## API

```rust
use geom::{PolytopeHRep, polytope_volume_hrep, systolic_ratio};

// Create polytope
let hrep = PolytopeHRep::new(normals, heights);
hrep.validate()?;

// Compute volume
let volume = polytope_volume_hrep(&hrep)?;

// After computing capacity with HK2017/Tube:
let sys = systolic_ratio(capacity, volume);
```

---

## Test Fixtures

Standard polytopes for testing. These are used across all algorithm crates.

### Naming Conventions

**2D Polygons:**
- `regular_ngon(n, r)` — Regular n-gon with circumradius r, first vertex at angle 0
- `rotated(polygon, θ)` — Rotate polygon CCW by θ radians

**4D Polytopes:**
- `lagrangian_product(Kq, Kp)` — Product K_q × K_p where K_q ⊂ ℝ²_q and K_p ⊂ ℝ²_p
- `unit_tesseract()` — The cube [-1,1]⁴
- `unit_cross_polytope()` — conv{±e₁, ±e₂, ±e₃, ±e₄}

**Parameterization:** Use circumradius (not inradius or edge length). Unit circumradius as default.

### Fixture Definitions

```rust
/// Regular n-gon with circumradius r
fn regular_ngon(n: usize, circumradius: f64) -> Polygon2D;

/// Rotate polygon CCW by angle (radians)
fn rotated(polygon: &Polygon2D, angle: f64) -> Polygon2D;

/// Lagrangian product K_q × K_p ⊂ ℝ⁴
fn lagrangian_product(Kq: &Polygon2D, Kp: &Polygon2D) -> PolytopeHRep;
```

### Standard Polytopes

| Fixture | Description | EHZ Capacity | Systolic Ratio |
|---------|-------------|--------------|----------------|
| `unit_tesseract()` | [-1,1]⁴ | 4.0 | < 1 |
| `unit_cross_polytope()` | 16 facets, vertices ±eᵢ | (tube computes) | < 1 |
| `equilateral_triangle_product()` | triangle × triangle | 1.5 | < 1 |
| `hko2024_counterexample()` | pentagon × rotated_pentagon | ≈ 3.441 | ≈ 1.047 |

**HK-O 2024 counterexample formula:**
```
c_EHZ = 2·cos(π/10)·(1 + cos(π/5)) ≈ 3.4409548
```

This is the counterexample to Viterbo's conjecture (systolic ratio > 1).

---

## Testing Strategy

| Test | Purpose | Location |
|------|---------|----------|
| Tesseract volume | Known value: 1.0 | `volume.rs:test_tesseract_volume` |
| Cross-polytope volume | Known value: 1/3 | `volume.rs:test_cross_polytope_volume` |
| Systolic ratio scaling | sys(λK) = sys(K) | `systolic.rs:test_systolic_ratio_scale_invariant` |
| Validation failures | Reject invalid input | `polytope.rs:test_*` |

---

## Dependencies

- `nalgebra`: Linear algebra (Vector4, Matrix4)
- `qhull`: Convex hull and Delaunay triangulation

---

## Related

- **HK2017 algorithm:** [hk2017/SPEC.md](../hk2017/SPEC.md)
- **Tube algorithm:** [tube/SPEC.md](../tube/SPEC.md)
- **Billiard algorithm:** [billiard/SPEC.md](../billiard/SPEC.md)
- **Comprehensive reference:** [developer-spec-v2.md](../docs/developer-spec-v2.md)
