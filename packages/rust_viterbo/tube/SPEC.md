# tube — Branch-and-Bound EHZ Capacity for Non-Lagrangian Polytopes

**Status:** Implementation complete, spec partially documented

## Purpose

Compute EHZ capacity for 4D convex polytopes with **no Lagrangian 2-faces**.

This algorithm organizes Reeb trajectories into "tubes" (sets of trajectories sharing a combinatorial class) and uses branch-and-bound to find the minimum-action closed orbit. For polytopes with mixed or all-Lagrangian 2-faces, use HK2017 instead.

## Applicability

| Polytope Type | 2-Face Character | Tube Algorithm |
|---------------|------------------|----------------|
| Cross-polytope, 24-cell | ALL non-Lagrangian | ✓ Applicable |
| Tesseract | ALL Lagrangian | ✗ Rejected |
| Lagrangian products | ALL Lagrangian | ✗ Rejected |
| Mixed polytopes | SOME Lagrangian | ✗ Rejected |

## Theoretical Foundation

**Sources:**
- **CH2021:** Chaidez-Hutchings, "Computing Reeb Dynamics on Four-Dimensional Convex Polytopes" — mathematical framework for Reeb dynamics, linear flows, symplectic flow graphs, rotation numbers
- **Thesis (Stöhler 2026), Section 4:** The "tube" data structure and branch-and-bound algorithm are original to this thesis

**Key insight:** For non-Lagrangian 2-faces, the Reeb flow direction is deterministic (no branching). This enables tracking trajectory families through their facet sequence rather than enumerating individual trajectories.

## Shared Definitions

The following definitions are shared with HK2017 and documented in [developer-spec-v2.md](../docs/developer-spec-v2.md):

| Concept | Spec Section | Code Location |
|---------|--------------|---------------|
| Polytope H-rep | §1.1 | `geom::PolytopeHRep` |
| Reeb vectors | §1.3 | `preprocess.rs:reeb_vector()` |
| Symplectic form ω | §1.4 | `quaternion.rs:symplectic_form()` |
| 2-faces and adjacency | §1.5 | `preprocess.rs:TwoFaceData` |
| Lagrangian vs non-Lagrangian | §1.6 | `constants::EPS_LAGRANGIAN` |
| Trivialization τ_F | §1.10 | `trivialization.rs` |
| Transition matrices ψ | §1.11 | `trivialization.rs:transition_matrix()` |
| Rotation number ρ | §1.12 | `trivialization.rs:rotation_number_from_trace()` |
| Action = period | §2.5 | `algorithm/reconstruct.rs` |

---

## Data Structures

### TwoFaceData

A **2-face** is the intersection of two adjacent facets F_entry ∩ F_exit. For non-Lagrangian 2-faces, ω(n_entry, n_exit) ≠ 0, so Reeb flow crosses in a deterministic direction.

```rust
pub struct TwoFaceData {
    pub entry_facet: usize,    // Facet we came from
    pub exit_facet: usize,     // Facet we flow into
    pub omega: f64,            // ω(n_entry, n_exit) > 0 (by convention)
    pub rotation: f64,         // ρ ∈ (0, 0.5)
    pub polygon: Polygon2D,    // 2-face in exit-trivialized coords
    pub centroid_4d: Vector4,  // For orbit reconstruction
    pub basis_exit: [Vector4; 2], // Trivialization basis
    // ...
}
```

**Invariant:** `omega > EPS_LAGRANGIAN` (rejects Lagrangian 2-faces)

**Code:** `types.rs:183-210`, `preprocess.rs:compute_two_faces()`

### ThreeFacetData

A **3-facet transition** (i, j, k) represents flowing on facet F_j from 2-face (F_i, F_j) to 2-face (F_j, F_k).

```rust
pub struct ThreeFacetData {
    pub two_face_entry: usize,  // Index of entry 2-face
    pub two_face_exit: usize,   // Index of exit 2-face
    pub facet_mid: usize,       // Middle facet (we flow along this)
    pub flow_matrix: Matrix2,   // A: maps entry coords → exit coords
    pub flow_offset: Vector2,   // b: affine offset
    pub time_gradient: Vector2, // ∇t for action computation
    pub time_constant: f64,     // Constant term in time function
}
```

**Mathematical meaning:** The flow map is `p_exit = A · p_entry + b` where A encodes the transition matrix ψ composed with the projection from one trivialization to another.

**Code:** `types.rs:212-234`, `preprocess.rs:compute_three_facets()`

### Tube

A **tube** represents all Reeb trajectories with a fixed combinatorial class (facet sequence).

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

**Code:** `types.rs:288-340`, `algorithm/mod.rs:extend_tube()`

### ClosedReebOrbit

The output: a closed piecewise-linear Reeb trajectory in 4D.

```rust
pub struct ClosedReebOrbit {
    pub period: f64,                    // T = action
    pub breakpoints: Vec<Vector4>,      // 4D positions, first = last
    pub segment_facets: Vec<usize>,     // Which facet for each segment
    pub segment_times: Vec<f64>,        // Duration of each segment
}
```

**Code:** `types.rs:342-353`, `algorithm/reconstruct.rs`

---

## Algorithm

### Overview

```
tube_capacity(K):
    data = preprocess(K)              // Compute 2-faces, transitions, trivializations
    if data.has_lagrangian_2faces:
        return Error(HasLagrangianTwoFaces)

    best_action = ∞
    worklist = PriorityQueue()        // Ordered by action lower bound

    // Initialize: one root tube per 2-face
    for two_face in data.two_faces:
        worklist.push(create_root_tube(two_face))

    // Branch and bound
    while tube = worklist.pop():
        if tube.action_lower_bound >= best_action:
            continue                  // Prune by action

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

1. **Empty tube:** `p_start.is_empty()` — no valid starting points remain
2. **Action bound:** `action_lower_bound() >= best_action` — cannot improve
3. **Rotation bound:** `rotation > 2.0 + EPS_ROTATION` — CH2021 Prop 1.10 proves minimum-action orbits have rotation ≤ 2

**Code:** `algorithm/mod.rs:78-82` (rotation), `algorithm/mod.rs:56` (action)

### Tube Extension

Extending a tube by one facet:
1. Look up valid transitions from the end 2-face
2. For each transition (j, k) where j = current end facet:
   - Compose the flow map: `new_flow = transition.flow_map ∘ tube.flow_map`
   - Compose the action function: `new_action = tube.action + transition.time_func`
   - Intersect p_end with the transition's entry polygon
   - Pull back the intersection through the flow map to get new p_start
   - Add the 2-face's rotation number

**Code:** `algorithm/mod.rs:extend_tube()`, `algorithm/mod.rs:create_extension()`

### Tube Closure

A tube is **closed** when `start_two_face() == end_two_face()`. Closure detection:

1. Check if the flow map `A - I` is invertible (det(A - I) ≠ 0)
2. If invertible: unique fixed point `x = (A - I)⁻¹ · b`
3. If near-singular (shear case): special handling for rank-1 matrix

**Code:** `algorithm/closure.rs:find_fixed_point()`, `algorithm/closure.rs:solve_regular_case()`

### Orbit Reconstruction

Given a 2D fixed point and closed tube, reconstruct the 4D orbit:

1. Convert start point to 4D using trivialization basis
2. For each segment, flow along the Reeb vector to the next 2-face
3. Compute segment times from displacements
4. Verify closure: final point ≈ start point

**Code:** `algorithm/reconstruct.rs:reconstruct_orbit()`

---

## Trivialization Details

The trivialization maps 2-face tangent spaces to ℝ² using the quaternion structure.

**CH2021 Definition 2.15:**
```
τ_F(V) = (⟨V, j·n_exit⟩, ⟨V, k·n_exit⟩)
```

where j, k are quaternion matrices satisfying j² = k² = -I, jk = i.

**Transition matrix:** ψ = τ_exit ∘ τ_entry⁻¹ ∈ Sp(2)

**Trace formula:** tr(ψ) = 2⟨n_entry, n_exit⟩

**Rotation number:** ρ = arccos(tr(ψ)/2) / 2π ∈ (0, 0.5)

**Derivation:** See [trivialization-derivation.md](../docs/trivialization-derivation.md)

**Code:** `trivialization.rs`, `quaternion.rs`

---

## API

```rust
use tube::{tube_capacity, PolytopeHRep, TubeResult, TubeError};

let hrep = PolytopeHRep::new(normals, heights);
match tube_capacity(&hrep) {
    Ok(result) => {
        println!("Capacity: {}", result.capacity);
        println!("Orbit period: {}", result.optimal_orbit.period);
    }
    Err(TubeError::HasLagrangianTwoFaces) => {
        println!("Use HK2017 instead");
    }
    Err(e) => eprintln!("Error: {}", e),
}
```

---

## Testing Strategy

### Correctness Tests

| Test | Purpose | Location |
|------|---------|----------|
| Cross-polytope capacity | Known value c=1.0 | `algorithm/mod.rs:test_tube_capacity_cross_polytope` |
| HK2017 comparison | Agreement on non-Lagrangian polytopes | `tests/hk2017_comparison.rs` |
| Orbit validity | Breakpoints on boundary, closure | `tests/orbit_invariants.rs` |
| Flow map symplectic | det(ψ) = 1 | `algorithm/mod.rs:test_flow_map_is_symplectic` |

### Property Tests

| Property | Formula | Test |
|----------|---------|------|
| Scaling | c(λK) = λ²c(K) | `tests/integration.rs:prop_scaling_law` |
| Action = period | A(γ) = Στᵢ | `tests/orbit_invariants.rs:test_action_equals_period` |
| Rotation bound | ρ_total ≤ 2 for optimal | `algorithm/mod.rs:test_root_tube_invariants` |

### Numerical Robustness

| Test | Purpose | Location |
|------|---------|----------|
| Small perturbations | Nearby polytopes → nearby capacities | `tests/flow_map_tests.rs:test_numerical_robustness_small_perturbation` |
| Multiple seeds | Deterministic results | `tests/flow_map_tests.rs:test_deterministic_results` |

---

## Constants and Tolerances

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

1. **Lagrangian 2-faces:** Algorithm rejects polytopes with any Lagrangian 2-faces. Use HK2017 for these.

2. **Shear case:** When det(A - I) ≈ 0 (flow map is nearly a shear), fixed-point detection requires special handling. Currently implemented but may have edge cases.

3. **Numerical tolerances:** The relationship between tolerances is not rigorously analyzed. Current approach: detect when numerics go wrong and error out.

4. **No independent ground truth:** Cross-polytope capacity (c=1.0) is verified via HK2017 comparison, not independent literature value.

---

## TODO

- [ ] Expand correctness proof in spec (why branch-and-bound covers all minimum-action orbits)
- [ ] Document tube invariants more precisely (p_start refinement, rotation accumulation)
- [ ] Add shear case analysis and edge case tests
- [ ] Reference mapping to thesis theorems

See developer-spec-v2.md §3.4 TODO block for details.

---

## Related

- **Shared spec:** [developer-spec-v2.md](../docs/developer-spec-v2.md)
- **Trivialization math:** [trivialization-derivation.md](../docs/trivialization-derivation.md)
- **Thesis:** `packages/latex_viterbo/chapters/algorithms.tex`
- **HK2017 algorithm:** `packages/rust_viterbo/hk2017/`
