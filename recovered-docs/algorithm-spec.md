# Capacity Algorithm Specification

This document is the **implementation guide** for the tube-based EHZ capacity algorithm.
Mathematical formulas are in [tube-geometry-spec.md](tube-geometry-spec.md).

> **Related:** For mathematical claims and citations, see `mathematical-claims.md` Section 3.3.

**Status:** Implementation exists but returns NoValidOrbits for all tested polytopes. See `code-audit-tracker.md`.

## 1. Goal

Compute the Ekeland-Hofer-Zehnder capacity c_EHZ(K) for a convex polytope K ⊂ ℝ⁴.

Return:
- Capacity value (f64)
- Witness orbit (breakpoints, facet sequence, segment times)
- Diagnostics (node counts, pruning stats, perturbation metadata)

## 2. Conventions (locked, from thesis)

- Coordinates: (q₁, q₂, p₁, p₂)
- Almost complex structure: J(q,p) = (-p, q)
- Symplectic form: ω(x,y) = ⟨Jx, y⟩
- H-rep: K = ∩ᵢ {x : ⟨nᵢ, x⟩ ≤ hᵢ} with unit normals nᵢ, heights hᵢ > 0

**Face notation:**
- Facets (3-faces): Eᵢ = {x ∈ K : ⟨nᵢ, x⟩ = hᵢ}
- 2-faces: Fᵢⱼ = Eᵢ ∩ Eⱼ

## 3. Input Contract

```rust
struct PolytopeHRep {
    normals: Vec<[f64; 4]>,  // unit outward normals
    heights: Vec<f64>,       // positive heights
}
```

**Invariants (validated at FFI boundary):**
- `normals.len() == heights.len()`
- All normals are unit vectors (‖nᵢ‖ = 1)
- All heights are positive (hᵢ > 0)
- No NaN/Inf values
- K is bounded and full-dimensional (implied by valid H-rep)
- 0 ∈ int(K) (implied by all heights positive)

## 4. Output Contract

```rust
struct CapacityResult {
    capacity: f64,
    witness: WitnessOrbit,
    diagnostics: Diagnostics,
}

struct WitnessOrbit {
    breakpoints: Vec<[f64; 4]>,  // cyclic list of corner points
    facet_sequence: Vec<usize>,  // facet index for each segment
    segment_times: Vec<f64>,     // time spent on each segment
}

struct Diagnostics {
    nodes_explored: u64,
    nodes_pruned_empty: u64,
    nodes_pruned_action: u64,
    nodes_pruned_rotation: u64,
    best_action_found: f64,
    perturbation: Option<PerturbationMetadata>,
}
```

## 5. Algorithm Overview

The algorithm searches over **combinatorial classes** of closed Reeb orbits.

Each orbit is characterized by a **facet sequence** (E₁, E₂, ..., Eₖ, E₁, E₂) that describes which facets the orbit visits. The orbit crosses 2-faces F₁₂ → F₂₃ → ... → Fₖ₁ → F₁₂.

We use **branch-and-bound**:
1. Enumerate partial orbits ("tubes") as a search tree
2. Prune tubes that cannot contain the minimum-action orbit
3. When a tube closes, compute its minimum action
4. Track the global minimum across all closed tubes

## 6. Data Structures

### 6.1 Precomputed Polytope Data

Before search, compute:

```rust
struct PolytopeData {
    hrep: PolytopeHRep,

    // For each 2-face Fᵢⱼ (only non-Lagrangian ones):
    two_faces: Vec<TwoFaceData>,
}

struct TwoFaceData {
    i: usize,                    // first facet index
    j: usize,                    // second facet index
    flow_direction: FlowDir,     // which way does flow cross?
    rotation: f64,               // ρ(Fᵢⱼ) in turns, ∈ (0, 0.5)
    vertices: Vec<[f64; 4]>,     // polygon vertices in ℝ⁴
}

enum FlowDir {
    ItoJ,  // flow crosses from Eᵢ into Eⱼ (ω(nᵢ, nⱼ) > 0)
    JtoI,  // flow crosses from Eⱼ into Eᵢ (ω(nᵢ, nⱼ) < 0)
}
```

### 6.2 Tube State

A tube represents a partial orbit. It tracks all trajectories consistent with a given facet sequence.

```rust
struct Tube {
    // Combinatorics
    facet_sequence: Vec<usize>,  // [i₁, i₂, ..., iₖ, iₖ₊₁]

    // Geometry (see tube-geometry-spec.md §5)
    p_start: Polygon2D,          // valid starting points (in TF₁₂ coordinates)
    p_end: Polygon2D,            // valid ending points (in TFₖ,ₖ₊₁ coordinates)
    flow_map: AffineMap2D,       // maps p_start → p_end
    action_func: AffineFunc,     // action as function of endpoint

    // Rotation tracking
    rotation: f64,               // total rotation so far (in turns)
}
```

**Key insight:** Both `p_start` and `p_end` are 2D polygons (in the tangent space of their respective 2-faces). The flow map and action function are affine.

## 7. Algorithm Pseudocode

### 7.1 Main Entry Point

```
function compute_capacity(hrep: PolytopeHRep) -> CapacityResult:
    // Step 1: Validate and preprocess
    validate(hrep)
    if has_lagrangian_2faces(hrep):
        hrep = perturb_normals(hrep, seed, epsilon)

    polytope_data = precompute(hrep)

    // Step 2: Initialize search
    best_action = +∞
    best_witness = None
    worklist = []  // priority queue by action lower bound

    // Step 3: Create root tubes (one per non-Lagrangian 2-face)
    for each 2-face Fᵢⱼ in polytope_data.two_faces:
        tube = create_root_tube(i, j, polytope_data)
        if tube.rotation <= 2 + ε_rot:
            worklist.push(tube)

    // Step 4: Branch-and-bound search
    while worklist is not empty:
        tube = worklist.pop_min_action()

        // Pruning check
        if action_lower_bound(tube) >= best_action:
            continue  // action pruning

        // Try to extend or close
        for each valid_extension in get_extensions(tube, polytope_data):
            match valid_extension:
                Extension(new_tube):
                    if new_tube.p_end is empty:
                        continue  // emptiness pruning
                    if new_tube.rotation > 2 + ε_rot:
                        continue  // rotation pruning
                    worklist.push(new_tube)

                Closure(closed_tube):
                    (action, witness) = solve_closed_tube(closed_tube)
                    if action < best_action:
                        best_action = action
                        best_witness = witness

    // Step 5: Return result
    return CapacityResult {
        capacity: best_action,
        witness: best_witness,
        diagnostics: collected_stats,
    }
```

### 7.2 Root Tube Creation

```
function create_root_tube(i: usize, j: usize, data: PolytopeData) -> Tube:
    // A root tube represents trajectories starting on 2-face Fᵢⱼ
    two_face = data.get_two_face(i, j)

    return Tube {
        facet_sequence: [i, j],
        p_start: two_face.vertices (as 2D polygon),
        p_end: two_face.vertices (as 2D polygon),
        flow_map: identity,
        action_func: constant 0,
        rotation: two_face.rotation,  // ρ(Fᵢⱼ)
    }
```

### 7.3 Tube Extension

```
function get_extensions(tube: Tube, data: PolytopeData) -> Vec<ExtensionResult>:
    results = []

    // Current state
    k = tube.facet_sequence.len() - 2      // second-to-last facet index position
    i_k = tube.facet_sequence[k]           // facet we're leaving
    i_k1 = tube.facet_sequence[k + 1]      // facet we're on

    // Check for immediately closable tube
    if i_k1 == tube.facet_sequence[0]:     // back at starting facet
        i_0 = tube.facet_sequence[0]
        i_1 = tube.facet_sequence[1]

        // Can only close by returning to starting 2-face F₀₁
        two_face = data.get_two_face(i_0, i_1)
        if flow_allows_crossing(i_k1, i_1, two_face.flow_direction):
            closed = extend_tube_to(tube, i_1, data)
            results.push(Closure(closed))
        return results  // no other extensions possible

    // Find all valid next facets
    for each 2-face Fⱼ adjacent to Eᵢₖ₊₁:
        j = other_facet_of(Fⱼ, i_k1)

        // Simplicity constraint: no repeated facets (except closing)
        if j in tube.facet_sequence[1..]:
            continue

        // Flow direction constraint
        two_face = data.get_two_face(i_k1, j)
        if not flow_allows_crossing(i_k1, j, two_face.flow_direction):
            continue

        // Extend the tube
        new_tube = extend_tube_to(tube, j, data)

        // Check if this extension closes the orbit
        if j == tube.facet_sequence[0] and
           can_close_to_start(new_tube, data):
            results.push(Closure(new_tube))
        else:
            results.push(Extension(new_tube))

    return results
```

### 7.4 Tube Extension Formulas

```
function extend_tube_to(tube: Tube, j: usize, data: PolytopeData) -> Tube:
    // Current ending 2-face: Fₖ,ₖ₊₁
    // New ending 2-face: Fₖ₊₁,ⱼ
    k1 = tube.facet_sequence.last()

    // Get flow map from Fₖ,ₖ₊₁ to Fₖ₊₁,ⱼ along facet Eₖ₊₁
    // (See tube-geometry-spec.md §3 for formulas)
    φ = compute_flow_map(k1, j, data)

    // Update geometry
    new_p_end = intersect(φ(tube.p_end), data.get_two_face(k1, j).vertices)
    new_flow_map = φ ∘ tube.flow_map
    new_action_func = tube.action_func + time_to_reach(k1, j)  // composed appropriately

    // Update rotation (additive!)
    new_rotation = tube.rotation + data.get_two_face(k1, j).rotation

    return Tube {
        facet_sequence: tube.facet_sequence.append(j),
        p_start: tube.p_start,  // unchanged
        p_end: new_p_end,
        flow_map: new_flow_map,
        action_func: new_action_func,
        rotation: new_rotation,
    }
```

### 7.5 Solving Closed Tubes

```
function solve_closed_tube(tube: Tube) -> (f64, WitnessOrbit):
    // A closed tube has facet_sequence [i₁, i₂, ..., iₖ, i₁, i₂]
    // The orbit must satisfy: starting point = ending point (periodicity)

    // Find fixed points of flow_map within p_end
    fixed_points = find_affine_fixed_points(tube.flow_map, tube.p_end)

    // Evaluate action at each fixed point
    min_action = +∞
    best_point = None
    for p in fixed_points:
        action = tube.action_func(p)
        if action < min_action:
            min_action = action
            best_point = p

    // Compute cyclic rotation (subtract double-counted starting 2-face)
    i₁, i₂ = tube.facet_sequence[0], tube.facet_sequence[1]
    cyclic_rotation = tube.rotation - data.get_two_face(i₁, i₂).rotation

    // Reconstruct witness orbit from best_point
    witness = reconstruct_orbit(tube, best_point)

    return (min_action, witness)
```

## 8. Key Implementation Details

### 8.1 2D Polygon Representation

Each 2-face tangent space TFᵢⱼ is a 2D symplectic vector space. We need a basis to represent polygons as 2D coordinates.

**Option A (recommended):** Use τ_F trivialization from tube-geometry-spec.md §4.2:
```
τ_F(V) = (⟨V, j·nⱼ⟩, ⟨V, k·nⱼ⟩)
```
where j, k are the quaternion matrices from `rust_viterbo_geom::quaternion`.

**Benefit:** The transition matrix ψ_F is already expressed in this basis.

### 8.2 Affine Map Representation

```rust
struct AffineMap2D {
    linear: [[f64; 2]; 2],  // 2×2 matrix
    offset: [f64; 2],       // translation
}

struct AffineFunc {
    gradient: [f64; 2],     // linear part
    constant: f64,          // constant part
}
```

### 8.3 Polygon Operations

Required operations:
1. **Intersection:** P ∩ Q (convex polygon intersection)
2. **Affine image:** φ(P) for affine map φ
3. **Emptiness test:** is P empty?
4. **Fixed point finding:** find p where φ(p) = p within P

For (4): φ(p) = p means (A - I)p + b = 0. If A - I is invertible, there's at most one fixed point. Check if it lies in P.

### 8.4 Flow Direction Logic

```
function flow_allows_crossing(from_facet: usize, to_facet: usize,
                               flow_dir: FlowDir) -> bool:
    // flow_dir describes Fᵢⱼ where i < j by convention
    // We need to check if flow goes from `from_facet` into `to_facet`

    if from_facet < to_facet:
        return flow_dir == ItoJ
    else:
        return flow_dir == JtoI
```

## 9. Pruning Rules

### 9.1 Emptiness Pruning
If `p_end` becomes empty after extension, prune. No valid orbit exists in this subtree.

### 9.2 Action Pruning
If the minimum possible action of any orbit in this tube exceeds the current best, prune.

**Action lower bound:** The action function is affine on `p_end`. The minimum over the polygon is achieved at a vertex or along an edge. Compute:
```
action_lower_bound(tube) = min(action_func(v) for v in p_end.vertices)
```

### 9.3 Rotation Pruning
If `rotation > 2 + ε_rot`, prune. Per CH2021, minimum-action orbits have rotation ≤ 2.

**Tolerance:** Use ε_rot = 0.01 (1% of a turn) to handle numerical error.

## 10. Lagrangian Perturbation

If any 2-face Fᵢⱼ has |ω(nᵢ, nⱼ)| ≤ ε_lagr, the polytope is "Lagrangian" and must be perturbed.

```
function perturb_normals(hrep: PolytopeHRep, seed: u64, epsilon: f64) -> PolytopeHRep:
    rng = seeded_rng(seed)
    new_normals = []
    for n in hrep.normals:
        delta = random_unit_vector(rng) * epsilon
        new_normals.push(normalize(n + delta))
    return PolytopeHRep { normals: new_normals, heights: hrep.heights }
```

**Parameters:**
- ε_lagr = 1e-9 (detection threshold)
- epsilon = 1e-6 (perturbation magnitude)
- seed: deterministic, passed through diagnostics

## 11. Testing Requirements

See original spec for detailed test requirements. Key tests:

### 11.1 Unit Tests (Rust)
- Quaternion relations (✓ implemented)
- J convention, ω antisymmetry (✓ implemented)
- Flow direction logic
- Affine map composition
- Polygon intersection

### 11.2 Integration Tests (Rust)
- Witness verification (points on ∂K, directions match Reeb)
- Determinism for non-Lagrangian inputs
- Known polytopes: simplex, cube, cross-polytope

### 11.3 Regression Tests (Python FFI)
- HK&O counterexample (known capacity value)
- FFI input validation

### 11.4 Property Tests
- Scaling: c(λK) = λ² c(K)
- Symplectic invariance (block rotations)
- Monotonicity: K ⊂ K' ⟹ c(K) ≤ c(K')

## 12. Implementation Milestones

1. **Polytope preprocessing:** 2-face extraction, flow direction, rotation computation
2. **Tube data structure:** polygon representation, affine maps, extension
3. **Search infrastructure:** worklist, pruning, closure detection
4. **Closed tube solver:** fixed point finding, action evaluation
5. **Witness reconstruction:** breakpoint extraction from solved tube
6. **Perturbation integration:** Lagrangian detection, seeded perturbation
7. **Diagnostics:** node counts, pruning stats, timing

## 13. References

- [tube-geometry-spec.md](tube-geometry-spec.md): Mathematical formulas for flow maps, rotation, trivializations
- CH2021: Chaidez-Hutchings, "Computing Reeb dynamics on four-dimensional convex polytopes"
- Thesis chapters on Reeb dynamics and the HK combinatorial formula
