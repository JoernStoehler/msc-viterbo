# Rust API Sketch (WIP / literal / TODO-marked)

Purpose: give a senior developer (math-savvy) enough structure to finalize types, traits, and modules for the 4D polytope EHZ/min-action work. Keep this as the single source of truth; mark all unknowns with `[TODO]` or `[SPECULATIVE]` so we don’t silently assume.

## Principles

- Use `nalgebra`
- Use readable names instead of mathematical symbols
- Layered structure: `geom` → `action` → `algo/*` → `sampling` → `ffi`
- Opinionated types that promise invariants, instead of raw types
- Clear error modes
- This document sketches signatures and types; you will probably want to deviate from the sketches in some places, for the sake of higher quality code.
- Convention for symplectic form: $\omega(v,w) = \langle v, Jw \rangle$ with standard $J = \begin{pmatrix}0 & -I \\ I & 0\end{pmatrix}$
- Facet Hamiltonian velocity: $p_F := (2/b_F) J n_F$ (HK2019); use this vector (not just its direction) in flow, exit-time, and action calculations to stay consistent with `02-algorithm.md`.

## Geom

- `Poly4` type: a compact, convex, star-shaped, non-degenerate polytope in $\mathbb{R}^4$; its representation is non-redundant and normalized.
  - `normals: Vec<Vector4<f64>>` ; $|n_i| = 1$
  - `offsets: Vec<f64>` ; $h_i > 0$
  - non-redundancy: there is no $i$ s.t. removing the half-space yields the same polytope
  - compactness: bounded i.e. no ray from the origin that never cuts a half-space
  - `vertices: Vec<Vector4<f64>>` ; non-redundant vertex list
  - non-redundancy: no vertex lies in or on the convex hull of the others
  - star-shaped: $0$ is in the interior
  - compatibility: both half-spaces and vertices match
  - `incidence: Matrix<bool>` ; `incidence[i,j] = true` iff vertex j lies on half-space i
  - `Poly4::is_valid(&self) -> bool` ; checks all invariants, should always be true for constructed Polys
  - `Poly4::from_hrep(normals: Vec<Vector4<f64>>, offsets: Vec<f64>) -> Result<Self, PolyError>` ; constructs and normalizes, or errors
  - `Poly4::from_vrep(vertices: Vec<Vector4<f64>>) -> Result<Self, PolyError>` ; constructs and normalizes, or errors

- Symplectic geometry
  - standard symplectic form `const omega: Matrix4<f64>` $(0 -I; I 0)$
  - check if a matrix is symplectic: `fn is_symplectic(m: &Matrix4<f64>, tol: f64) -> bool`
  - decompose $Sp(2n) = S_+ Sp(2n) \times U(n)$ for $n=1$
    - `fn decompose_symplectic(m: &Matrix2<f64>) -> (Matrix2<f64>, Complex<f64>)` where the first is in $S_+ Sp(2)$ and the second in $U(1)$
    - `fn rotation_from_symplectic(m: &Matrix2<f64>) -> f64` returning angle in $[0, 2\pi)$
  - given a plane spanned by 2 vectors, find 2 basis vectors that are symplectic-orthogonal
    - `fn symplectic_orthogonal_basis(v1: &Vector4<f64>, v2: &Vector4<f64>) -> (Vector4<f64>, Vector4<f64>)`

- `Affine4x2<f64>, Affine4<f64>, Affine2x4<f64>, Affine2<f64>` types for affine maps between $\mathbb{R}^n \to \mathbb{R}^m$ with methods to apply them to points/vectors, to compose them.

## Our Algorithm

- We assume an ambient `Poly4` as context, with no lagrangian 2-faces (reject on construction). Branch-and-bound relies on the non-Lagrangian ridge property.
- We build the 2-face node graph

- `Poly2` type: a convex non-empty polygon in $\mathbb{R}^2$
  - `vertices`: `Vec<Vector2<f64>>` ; CCW order, non-redundant
  - `normals`: `Vec<Vector2<f64>>` ; unit-length, outward-pointing
  - `offsets`: `Vec<f64>` can now be negative
  - `Poly2::from_hrep(normals: Vec<Vector2<f64>>, offsets: Vec<f64>) -> Result<Self, PolyError>` ; constructs and normalizes, or errors
  - `Poly2::from_vrep(vertices: Vec<Vector2<f64>>) -> Result<Self, PolyError>` ; constructs and normalizes, or errors
  - `Poly2::is_valid(&self) -> bool` ; checks all invariants, should always be true for constructed Polys

- `Face2Node`
  - `facets: (usize, usize)` ; indices into Poly4.normals ; flow goes from facet 0 to facet 1
  - `projection: Affine2x4<f64>` ; projects points onto their 2D coords in this face; rows are orthonormal symplectic basis vectors; constraint $\omega(p_1, p_2) = 1$
  - `inverse_projection: Affine4x2<f64>` ; lifts 2D coords back into $\mathbb{R}^4$ in this face
  - `rotation: f64` ; CZ-related rotation when flowing through this face

- `Face2Edge`
  - `indices: (usize, usize)` ; indices into `Vec<Face2Node>` ; (start, end)
  - `facet: usize` ; index into Poly4.normals ; the shared 3-face
  - `normal: Vector4<f64>` ; the normal of the shared 3-face
  - `velocity: Vector4<f64>` ; facet Hamiltonian velocity $p_F = (2/b_F) J n$ used for exit-time and action
  - `flow: Affine2<f64>` ; the affine map in 2D coords when crossing this edge
  - `inverse_flow: Affine2<f64>` ; the inverse affine map in 2D coords when crossing this edge
  - `domain: Poly2, image: Poly2` ; of the flow map in 2D coords
  - `action: Affine1x2<f64>` ; computes action increment when crossing this edge; image to R;
  - `lower_bound_action: f64` ; $\min_{x \in \text{image}} \text{action}(x)$

- `FlowMapGraph`
  - `nodes: Vec<Face2Node>`
  - `edges: Vec<Face2Edge>`
  - `incidence: Matrix<bool>` ; `incidence[i,j] = true` iff edge j starts at node i
  - `adjacency: Matrix<bool>` ; `adjacency[i,j] = true` iff there is an edge from node i to node j
  - `next: Vec<Vec<(usize,usize)>>` ; `next[i][*] = (k, facets.1 of nodes[indices.1 of edges[k]])` ; the facet that will be crossed on the next step after taking edge k from node i
  - `FlowMapGraph::from_poly4(poly: &Poly4) -> Result<Self, GraphError>` ; builds the graph from the polytope, or errors if lagrangian 2-faces are present
  - `FlowMapGraph::without_node(&self, node_index: usize) -> Self` ; returns a new graph with the given node and its incident edges removed; useful for exhaustive search over the starting face

- `State`: internal state during branch-and-bound search
  - `visited: BitSet` ; set of traversed facets
  - `flow: Affine2<f64>` ; current overall flow map in 2D coords
  - `image: Poly2` ; remaining image in 2D coords
  - `action: Affine1x2<f64>` ; current overall action functional, image to R
  - `rotation: f64` ; accumulated rotation

- Algorithmic step:
  - `append_edge(state: &State, edge: &Face2Edge, current_best_action: f64) -> Option<State>` ; tries to append the edge to the current state; returns new state or None if image becomes empty
    - flow' = edge.flow * flow
    - image* = edge.flow(image) \cap edge.image
    - action' = edge.action + action * edge.inverse_flow
    - rotation' = rotation + edge.rotation
    - image' = image* \cap {action' <= current_best_action}
    - if rotation' >= 2.0 (CZ-bound), return None
    - if image' is finally empty, return None
    - else return Some(State { flow', image', action', rotation' })

- Main solver:
  - build `FlowMapGraph` from input `Poly4`
  - candidate orbit = dummy; best_action = upper bound from enclosing ball
  - loop over starting nodes; remove starting node from graph at the end
    - initialize state
    - recursive branch-and-bound search:
      - append an edge
      - update state
      - if image empty, backtrack
      - else if closed (current node == starting node)
        - if fixed point exists
          - replace candidate
        - else backtrack
      - else: continue appending edges
    - end loop
  - return best candidate found and post-process into an explicit orbit: ordered boundary points (one per ridge crossing) forming the piecewise-linear closed characteristic in $\mathbb{R}^4$.

- Which edge(s) to append?
  - `graph.next[nodes[last]].0` gives all outgoing edges
  - if we can close the orbit, try only that edge, since if we don't use it we will never be able to close later
  - remove edges that lead to a node that flows into an already traversed facet (this anticipates violations of the visit-once rule); simply done by looking `graph.next[nodes[last]][*].1` and visited `facets`

## Modules
- `geom`: basic symplectic helpers and canonical symbols:
- `geom/action`: definitions/validation (action functional, systolic ratio from capacity, ...).
- `algo/custom`: our branch-and-bound + flow-map solver for min-action; enforces non-lagrangian input and rotation < 2 pruning.
- `algo/heim_kislev_2019`: LP-based solver.
- `algo/chadez_hutchings_2021`: baseline solver.
- `algo/minkowski_billiard_2024`: special-case solver for Lagrangian products.
- `sampling`: random polytope generators; known cases (orthonormal simplex, cube, crosspolytope, standard counterexample); enumeration (lagrangian products of rotated regular polygons).
- `ffi`: PyO3 bindings

## Sampling / Fixtures
- Return None on failure (not compact, degenerate, not star-shaped, ...).
- Functions:
  - `uniform_normal_offset(seed, num_halfspaces) -> Option<Poly4>`
    - normals: uniform on $S^3$
    - offsets: uniform in `[0.5, 1.5]`
- Known cases (must be non-lagrangian or slightly perturbed to become so):
  - `orthonormal_simplex() -> Poly4`; translated so $0$ is in the interior
  - `cube() -> Poly4`
  - `crosspolytope() -> Poly4`
  - `standard_counterexample_approx() -> Poly4` (small perturbation of the HK–Ostrover pentagon product to remove lagrangian ridges)
  - also have `capacity_*, volume_*, systolic_ratio_*` constants for these
- Enumeration:
  - `lagrangian_product_of_rotated_polygons(n: usize, m: usize, angle: f64) -> Poly4`
    - builds $P_n \times e^{i \theta} P_m$ where $P_k$ is the regular k-gon inscribed in the unit circle
    - angle in radians

## Testing Expectations
- Unit/property tests in Rust: 
  - constructing Polys from valid/invalid H-reps and V-reps
  - is_symplectic for known symplectic/non-symplectic matrices
  - affine math
  - known case flow map graph (since most our examples have lagrangian 2-faces, we need to make up a small non-lagrangian polytope for this)
  - edge appending logic
  - important: final capacity for known cases (again: we may need to make up new, or wiggle lagrangian cases (who then become non-lagrangian and change only slightly their capacity))
  - important: volume for known cases
  - samplers produce valid Polys
- important: computed action agrees with a separate calculation of the action using the returned orbit
- important: returned orbit lies on the polytope boundary; returned point list matches the face sequence
- final capacity remains unchanged under applying a symplectomorphism to the input polytope (you can pick a random input polytope that's non-lagrangian)

## FFI Surface (Python)
- Python numpy-based types for `Poly4` and `Orbit` (orbit includes ordered boundary points and per-segment face indices)
- Wrappers of samplers, volume, capacity, systolic ratio, action-of-orbit
- It's okay to do e.g. matrix * poly multiplication in numpy without using FFI

## Documentation hooks
- Every public type/function to carry docstrings pointing back to thesis sections `docs/draft/` rn holds the most up-to-date versions.
- Keep a short “contract” comment in code: invariants, units, expected tolerances.

## Outputs (Rust types)
- `CapacityResult` (for the custom solver):
  - `capacity: f64` ($c_{\mathrm{EHZ}}$)
  - `action: f64` (should equal `capacity` by definition; included for clarity)
  - `orbit: Orbit`
  - `diagnostics: Option<Diag>` (iterations, explored nodes, best_bound, etc.; fill as needed)
- `Orbit`:
  - `points: Vec<Vector4<f64>>` in cyclic order, lying on $\partial K$
  - `faces: Vec<usize>` parallel to points, each the facet index whose interior segment is traversed next
  - `ridges: Vec<usize>` optional; ridge index for each point
  - `action: f64`
  - `rotation: f64`

## Open questions to resolve (fill before implementation)
- [TODO] Exact H-rep normalization: do we require `||n_i||=1`? do we renormalize internally?
  - YES we require; we do not silently renormalize but error
- [TODO] What diagnostic fields are mandatory in `CapacityResult`? (iterations, best_bound, explored_nodes?)
  - UNSURE, for now not a priority, add as you go while you debug errors and hotspots; mind that only debug builds should pay for the diagnostic fields
- [TODO] Preferred LP backend for HK2019; acceptable licenses.
  - postponed
- [TODO] Feature gating for f128/interval: which crates? how to select per-call?
  - postponed
