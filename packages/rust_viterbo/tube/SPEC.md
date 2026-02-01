# tube — Branch-and-Bound EHZ Capacity for Non-Lagrangian Polytopes

**Status:** Implementation complete

## Purpose

Compute EHZ capacity for 4D convex polytopes with **no Lagrangian 2-faces**.

This algorithm organizes Reeb trajectories into "tubes" (sets of trajectories sharing a combinatorial class) and uses branch-and-bound to find the minimum-action closed orbit.

## Applicability

| Polytope Type | 2-Face Character | Tube Algorithm |
|---------------|------------------|----------------|
| Cross-polytope, 24-cell | ALL non-Lagrangian | ✓ Applicable |
| Tesseract | ALL Lagrangian | ✗ Rejected |
| Lagrangian products | ALL Lagrangian | ✗ Rejected |
| Mixed polytopes | SOME Lagrangian | ✗ Rejected |

For polytopes with Lagrangian 2-faces, use HK2017 or Billiard instead.

## Theoretical Foundation

**Sources:**
- **CH2021:** Chaidez-Hutchings, "Computing Reeb Dynamics on Four-Dimensional Convex Polytopes" — Reeb dynamics, linear flows, quaternion trivialization, rotation numbers
- **Thesis (Stöhler 2026), Section 4:** The "tube" data structure and branch-and-bound algorithm

**Key insight:** For non-Lagrangian 2-faces, Reeb flow direction is deterministic (no branching). This enables tracking trajectory families through their facet sequence.

---

## Quaternion Structure

**Source:** CH2021 §2.3 (quaternionic trivialization)

The quaternion matrices **i**, **j**, **k** ∈ SO(4) satisfy:
- i² = j² = k² = -I
- ij = k, jk = i, ki = j
- **i** is the standard almost complex structure (symplectic J)

Explicit matrices (coordinates x₁, x₂, y₁, y₂):

```
         ⎡ 0  0 -1  0 ⎤          ⎡ 0 -1  0  0 ⎤          ⎡ 0  0  0 -1 ⎤
QUAT_I = ⎢ 0  0  0 -1 ⎥  QUAT_J = ⎢ 1  0  0  0 ⎥  QUAT_K = ⎢ 0  0  1  0 ⎥
         ⎢ 1  0  0  0 ⎥          ⎢ 0  0  0  1 ⎥          ⎢ 0 -1  0  0 ⎥
         ⎣ 0  1  0  0 ⎦          ⎣ 0  0 -1  0 ⎦          ⎣ 1  0  0  0 ⎦
```

**Key properties:**
- ω₀(u, v) = ⟨QUAT_I · u, v⟩ (symplectic form)
- ω₀(QUAT_J · ν, QUAT_K · ν) = 1 for any unit vector ν
- {QUAT_I · ν, QUAT_J · ν, QUAT_K · ν} is orthonormal for any unit ν

```rust
fn symplectic_form(u: &Vector4<f64>, v: &Vector4<f64>) -> f64 {
    (QUAT_I * u).dot(v)
}

fn reeb_vector(normal: &Vector4<f64>, height: f64) -> Vector4<f64> {
    (QUAT_I * normal) * (2.0 / height)
}
```

**Code:** `quaternion.rs`

---

## Trivialization of 2-Face Tangent Spaces

**Source:** CH2021 Definition 2.15, Lemma 2.16

### The Trivialization Map τ

For a 2-face F at intersection of facets with normals n_entry and n_exit, the tangent space is:
```
TF = { V ∈ ℝ⁴ : ⟨V, n_entry⟩ = 0 and ⟨V, n_exit⟩ = 0 }
```

The trivialization τ_n: TF → ℝ² with respect to unit normal n (CH2021 Definition 2.15):
```
τ_n(V) = (⟨V, QUAT_J · n⟩, ⟨V, QUAT_K · n⟩)
```

**Convention (CH2021):** Use the EXIT facet's normal for trivialization.

```rust
fn trivialize(n: &Vector4<f64>, v: &Vector4<f64>) -> Vector2<f64> {
    let jn = QUAT_J * n;
    let kn = QUAT_K * n;
    Vector2::new(v.dot(&jn), v.dot(&kn))
}
```

**Code:** `trivialization.rs:trivialize()`

### Why Trivialization Fails for Lagrangian 2-Faces

When ω(n₁, n₂) = ⟨QUAT_I · n₁, n₂⟩ = 0:
- The vector QUAT_I · n₁ is perpendicular to n₂ (and already perpendicular to n₁)
- So QUAT_I · n₁ lies in the 2-face tangent space TF
- The 2-face projects to a 1D line → **degenerate**

This degeneracy is why the tube algorithm cannot handle Lagrangian 2-faces.

### Explicit Basis Vectors for Reconstruction

**Source:** Derived from CH2021 Definition 2.15. See `trivialization-derivation.md`.

To convert 2D coordinates back to 4D, we need basis vectors b₁, b₂ ∈ TF such that:
- τ_{n_exit}(b₁) = (1, 0)
- τ_{n_exit}(b₂) = (0, 1)

**Matrix formulation:** Define M_exit with rows [n_entry, n_exit, QUAT_J · n_exit, QUAT_K · n_exit]:
```
b₁ = 3rd column of M_exit⁻¹
b₂ = 4th column of M_exit⁻¹
```

```rust
fn compute_exit_basis(n_entry: &Vector4<f64>, n_exit: &Vector4<f64>) -> [Vector4<f64>; 2] {
    let jn_exit = QUAT_J * n_exit;
    let kn_exit = QUAT_K * n_exit;

    let m = Matrix4::from_rows(&[
        n_entry.transpose(),
        n_exit.transpose(),
        jn_exit.transpose(),
        kn_exit.transpose(),
    ]);

    let m_inv = m.try_inverse().expect("Degenerate 2-face");
    [m_inv.column(2).into(), m_inv.column(3).into()]
}
```

**Reconstruction:**
```rust
fn untrivialize(coords: &Vector2<f64>, basis: &[Vector4<f64>; 2], centroid: &Vector4<f64>) -> Vector4<f64> {
    centroid + coords[0] * basis[0] + coords[1] * basis[1]
}
```

**Code:** `trivialization.rs:compute_exit_basis()`, `algorithm/reconstruct.rs:untrivialize_point()`

---

## Transition Matrices

**Source:** CH2021 Definition 2.17, Lemma 2.18

The transition matrix ψ_F ∈ Sp(2) converts entry-trivialized to exit-trivialized coordinates:
```
ψ_F = τ_{n_exit} ∘ τ_{n_entry}⁻¹
```

### Computation Methods

**Method A (explicit basis):**
```rust
fn transition_matrix_from_basis(b_entry: &[Vector4; 2], n_exit: &Vector4) -> Matrix2<f64> {
    let jn_exit = QUAT_J * n_exit;
    let kn_exit = QUAT_K * n_exit;

    Matrix2::new(
        b_entry[0].dot(&jn_exit), b_entry[1].dot(&jn_exit),
        b_entry[0].dot(&kn_exit), b_entry[1].dot(&kn_exit),
    )
}
```

**Method B (CH2021 Lemma 2.17 formula):**

Let:
```
a₁ = ⟨n_entry, n_exit⟩
a₂ = ⟨QUAT_I · n_entry, n_exit⟩
a₃ = ⟨QUAT_J · n_entry, n_exit⟩
a₄ = ⟨QUAT_K · n_entry, n_exit⟩
```

Then:
```
        1   ⎡ a₁a₂ - a₃a₄    -(a₂² + a₄²) ⎤
ψ_F = ─── · ⎢                              ⎥
       a₂   ⎣  a₂² + a₃²      a₁a₂ + a₃a₄  ⎦
```

**Properties:**
- det(ψ_F) = 1 (symplectic)
- tr(ψ_F) = 2⟨n_entry, n_exit⟩
- a₂ > 0 by flow direction convention

**Code:** `trivialization.rs:transition_matrix()`, `trivialization.rs:transition_matrix_ch2021()`

---

## Rotation Number

**Source:** CH2021 Appendix A, Lemma 2.17

For a non-Lagrangian 2-face F:
```
ρ(F) = (1/2π) · arccos(tr(ψ_F)/2) = (1/2π) · arccos(⟨n_entry, n_exit⟩)
```

**Range:** ρ ∈ (0, 0.5) for non-Lagrangian 2-faces.

**Derivation:** For a 2×2 symplectic matrix ψ (det = 1), the trace satisfies tr(ψ) = 2cos(2πρ) where ρ is the rotation number. Since tr(ψ) = 2⟨n_entry, n_exit⟩ for polytope 2-faces, inverting gives ρ = arccos(tr(ψ)/2) / 2π.

```rust
pub fn rotation_number_from_trace(trace: f64) -> f64 {
    debug_assert!(trace.abs() <= 2.0 + EPS, "trace out of valid range: {}", trace);
    let half_trace = (0.5 * trace).clamp(-1.0 + EPS, 1.0 - EPS);
    half_trace.acos() / (2.0 * std::f64::consts::PI)
}
```

**Code:** `trivialization.rs:rotation_number_from_trace()`

**Significance (CH2021 Prop 1.8):**
- Every Reeb orbit has total rotation > 1 turn
- Action-minimizing orbits have rotation ≤ 2 turns
- Algorithm prunes paths exceeding 2 turns

---

## Data Structures

### TwoFaceData

```rust
pub struct TwoFaceData {
    pub entry_facet: usize,         // Facet we came from
    pub exit_facet: usize,          // Facet we flow into
    pub omega: f64,                 // ω(n_entry, n_exit) > 0 (by convention)
    pub rotation: f64,              // ρ ∈ (0, 0.5)
    pub polygon: Polygon2D,         // 2-face in exit-trivialized coords
    pub centroid_4d: Vector4<f64>,  // For orbit reconstruction
    pub basis_exit: [Vector4<f64>; 2], // Trivialization basis
    pub entry_normal: Vector4<f64>,
    pub exit_normal: Vector4<f64>,
}
```

**Invariant:** `omega > EPS_LAGRANGIAN` (rejects Lagrangian 2-faces)

**Code:** `types.rs:183-210`, `preprocess.rs`

### ThreeFacetData

A 3-facet transition (i, j, k) represents flowing on facet F_j from 2-face (F_i, F_j) to 2-face (F_j, F_k).

```rust
pub struct ThreeFacetData {
    pub two_face_entry: usize,   // Index of entry 2-face
    pub two_face_exit: usize,    // Index of exit 2-face
    pub facet_mid: usize,        // Middle facet (we flow along this)
    pub flow_matrix: Matrix2,    // A: maps entry coords → exit coords
    pub flow_offset: Vector2,    // b: affine offset
    pub time_gradient: Vector2,  // ∇t for action computation
    pub time_constant: f64,      // Constant term in time function
}
```

**Flow map:** p_exit = A · p_entry + b

**Code:** `types.rs:212-234`, `preprocess.rs`

### Tube

```rust
pub struct Tube {
    pub facet_sequence: Vec<usize>,  // [i₀, i₁, ..., iₖ, iₖ₊₁]
    pub p_start: Polygon2D,          // Valid starting points
    pub p_end: Polygon2D,            // Valid ending points
    pub flow_map: AffineMap2D,       // Maps start → end
    pub action_func: AffineFunc,     // Action as function of start point
    pub rotation: f64,               // Accumulated rotation (in turns)
}
```

**Invariants:**
- `p_start` = pullback of 2-face polygons through all transitions
- `flow_map` = composition of all ThreeFacetData flow maps
- `action_func` = sum of all segment time functions
- `rotation` = sum of all 2-face rotation numbers

**Code:** `types.rs:288-340`

### ClosedReebOrbit

```rust
pub struct ClosedReebOrbit {
    pub period: f64,                    // T = action
    pub breakpoints: Vec<Vector4<f64>>, // 4D positions, first = last
    pub segment_facets: Vec<usize>,     // Which facet for each segment
    pub segment_times: Vec<f64>,        // Duration of each segment
}
```

**Code:** `types.rs:342-353`

---

## Flow Map Derivation

For a point p_2d = (a, b) in entry 2-face coordinates:

1. **Convert to 4D:** p_4d = c_entry + a · b_entry[0] + b · b_entry[1]

2. **Compute time to reach exit hyperplane:**
   ```
   t = (h_next - ⟨p_4d, n_next⟩) / ⟨R_curr, n_next⟩
   ```
   Time function: t(p_2d) = t_const + ⟨t_grad, p_2d⟩

3. **Flow:** q_4d = p_4d + t · R_curr

4. **Convert to exit coords:** q_2d = (⟨q_4d - c_exit, jn_exit⟩, ⟨q_4d - c_exit, kn_exit⟩)

**Result:** q_2d = A · p_2d + b where:
```
A = ψ + r_triv ⊗ t_grad
b = τ_exit(c_entry - c_exit + t_const · R_curr)
```

**Assertion:** det(A) = 1 (flow map is symplectic/area-preserving)

**Code:** `preprocess.rs`

---

## Algorithm

```
tube_capacity(K):
    data = preprocess(K)
    if data.has_lagrangian_two_faces:
        return Error(HasLagrangianTwoFaces)

    best_action = ∞
    worklist = PriorityQueue()  // Ordered by action lower bound

    // Initialize: one root tube per 2-face
    for two_face in data.two_faces:
        worklist.push(create_root_tube(two_face))

    // Branch and bound
    while tube = worklist.pop():
        if tube.action_lower_bound >= best_action:
            continue  // Prune by action

        for extension in get_extensions(tube, data):
            if extension.is_closed():
                fixed_point = find_fixed_point(extension)
                if fixed_point exists and in valid region:
                    action = extension.action_func.eval(fixed_point)
                    if action < best_action:
                        best_action = action
                        best_orbit = reconstruct_orbit(fixed_point, extension)
            else:
                if extension.rotation <= 2.0 + ε:
                    worklist.push(extension)

    return best_action
```

**Code:** `algorithm/mod.rs:tube_capacity()`

### Pruning Rules

1. **Empty tube:** `p_start.is_empty()` — no valid starting points
2. **Action bound:** `action_lower_bound() >= best_action` — cannot improve
3. **Rotation bound:** `rotation > 2.0 + EPS_ROTATION` — CH2021 Prop 1.10

### Facet Sequence Constraints

**Minimum closed tube length is 5:**

A closed tube requires at least 3 distinct facets, giving minimum sequence length 5: [i₀, i₁, i₂, i₀, i₁].

*Proof:* Length 4 [i, j, i, j] would require flow i→j at F_{i,j}, then j→i at F_{j,i} = F_{i,j}. But flow direction is fixed by ω(nᵢ, nⱼ): if ω > 0, flow always goes i→j. By antisymmetry, flow cannot reverse at the same 2-face. □

### Tube Extension

```rust
fn extend_tube(tube: &Tube, next_facet: usize, data: &PolytopeData) -> Option<Tube> {
    let (phi, time_func) = compute_facet_flow(tube, next_facet, data);

    // Intersect flow-mapped p_end with exit 2-face polygon
    let new_p_end = intersect_polygons(&apply_affine(&phi, &tube.p_end), &exit_polygon);

    if new_p_end.is_empty() {
        return None;
    }

    Some(Tube {
        facet_sequence: tube.facet_sequence + [next_facet],
        p_start: tube.p_start.clone(),
        p_end: new_p_end,
        flow_map: compose(phi, tube.flow_map),
        action_func: tube.action_func + compose(time_func, tube.flow_map),
        rotation: tube.rotation + exit_two_face.rotation,
    })
}
```

**Code:** `algorithm/mod.rs:extend_tube()`

### Tube Closure

For a closed tube (start 2-face = end 2-face), find fixed points of the flow map:
```
ψ(s) = s  ⟺  (A - I)s = -b
```

**Regular case (det(A-I) ≠ 0):** Unique fixed point s = (A - I)⁻¹(-b)

**Shear case (det(A-I) ≈ 0):** The flow map is nearly a shear transformation. Handle via rank analysis of (A - I).

**Code:** `algorithm/closure.rs:find_fixed_point()`

### Orbit Reconstruction

Given 2D fixed point and closed tube, reconstruct 4D orbit:

1. Convert start point to 4D using trivialization basis
2. For each segment, flow along Reeb vector to next 2-face
3. Compute segment times: t = ⟨displacement, R⟩ / ‖R‖²
4. Verify closure: ‖final - start‖ < EPS_CLOSURE

**Code:** `algorithm/reconstruct.rs:reconstruct_orbit()`

---

## Geometry Utilities

### Polygon Intersection (Sutherland-Hodgman)

```rust
pub fn intersect_polygons(p1: &Polygon2D, p2: &Polygon2D) -> Polygon2D {
    // Clip p1 against each edge of p2
    let mut result = p1.vertices.clone();
    for edge in p2.edges() {
        result = clip_by_halfplane(&result, edge);
    }
    Polygon2D::new(result)
}
```

**Code:** `geometry.rs:intersect_polygons()`

### Point-in-Polygon Test

```rust
pub fn point_in_polygon(p: &Vector2<f64>, polygon: &Polygon2D) -> bool {
    // For convex polygons: point is inside iff left of all edges
    polygon.edges().all(|edge| is_left_of_edge(p, edge))
}
```

**Code:** `geometry.rs:point_in_polygon()`

---

## API

```rust
use tube::{tube_capacity, PolytopeHRep, TubeResult, TubeError};

let hrep = PolytopeHRep::new(normals, heights);
match tube_capacity(&hrep) {
    Ok(result) => {
        println!("Capacity: {}", result.capacity);
        println!("Orbit period: {}", result.optimal_orbit.period);
        println!("Tubes explored: {}", result.tubes_explored);
    }
    Err(TubeError::HasLagrangianTwoFaces) => {
        println!("Use HK2017 instead");
    }
    Err(e) => eprintln!("Error: {}", e),
}
```

---

## Testing Strategy

### Ground Truth

| Test | Expected | Location |
|------|----------|----------|
| Cross-polytope | c = 1.0 | `test_tube_capacity_cross_polytope` |
| HK2017 agreement | ratio ≈ 1.0 | `tests/hk2017_comparison.rs` |

### Property Tests

| Property | Formula | Location |
|----------|---------|----------|
| Scaling | c(λK) = λ²c(K) | `tests/integration.rs` |
| Action = period | A(γ) = Στᵢ | `tests/orbit_invariants.rs` |
| Rotation bound | ρ_total ≤ 2 for optimal | `test_root_tube_invariants` |

### Invariant Tests

| Test | Purpose | Location |
|------|---------|----------|
| Flow map symplectic | det(ψ) = 1 | `test_flow_map_is_symplectic` |
| Transition matrix trace | tr(ψ) = 2⟨n₁,n₂⟩ | `test_transition_matrix_trace_formula` |
| Basis in tangent space | b·n = 0 | `test_trivialize_round_trip` |
| Methods agree | CH2021 = basis method | `test_transition_matrix_methods_agree` |

---

## Constants

| Constant | Value | Purpose |
|----------|-------|---------|
| `EPS` | 1e-10 | General floating-point comparison |
| `EPS_LAGRANGIAN` | 1e-8 | Threshold for Lagrangian detection |
| `EPS_ROTATION` | 0.01 | Tolerance for rotation pruning |
| `EPS_CLOSURE` | 1e-6 | Orbit closure verification |
| `EPS_SINGULAR` | 1e-8 | Near-singular flow map detection |

**Code:** `constants.rs`

---

## Known Limitations

1. **Lagrangian 2-faces:** Rejects polytopes with any Lagrangian 2-faces

2. **Shear case:** When det(A - I) ≈ 0, fixed-point detection requires special handling

3. **Numerical tolerances:** Relationship between tolerances not rigorously analyzed

4. **No independent ground truth:** Cross-polytope capacity verified via HK2017 comparison

---

## Related

- **Shared primitives:** `packages/rust_viterbo/geom/`
- **HK2017 algorithm:** `packages/rust_viterbo/hk2017/`
- **Trivialization derivation:** `docs/trivialization-derivation.md`
- **Thesis:** `packages/latex_viterbo/chapters/algorithms.tex`
