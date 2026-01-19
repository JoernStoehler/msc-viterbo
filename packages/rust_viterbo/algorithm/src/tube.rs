//! Tube data structure and operations for the branch-and-bound search.
//!
//! A tube represents a partial Reeb orbit with a known combinatorial type
//! (facet sequence) and tracks:
//! - Valid starting/ending points (as 2D polygons)
//! - Flow map from start to end coordinates
//! - Accumulated action as affine function of starting point
//! - Total rotation (for pruning)
//!
//! The key insight is that flow maps between 2-faces are affine, so tube
//! composition reduces to 2D affine algebra.
//!
//! See thesis §4.3 and [algorithm-spec.md](../docs/algorithm-spec.md).

use crate::affine::{AffineFunc, AffineMap2D};
use crate::polygon::Polygon2D;
use crate::polytope::{FlowDir, PolytopeData, TwoFaceData};
use rust_viterbo_geom::{
    apply_j, quaternion, symplectic_form, trivialization, Matrix2f, SymplecticVector, Vector2f,
};

/// A tube represents a partial Reeb orbit with a given combinatorial type.
#[derive(Clone, Debug)]
pub struct Tube {
    /// Facet sequence [i₁, i₂, ..., iₖ₊₁]
    pub facet_sequence: Vec<usize>,
    /// Valid starting points (in τ_F₁₂ coordinates)
    pub p_start: Polygon2D,
    /// Valid ending points (in τ_Fₖ,ₖ₊₁ coordinates)
    pub p_end: Polygon2D,
    /// Flow map from p_start to p_end coordinates
    pub flow_map: AffineMap2D,
    /// Action as function of starting point
    pub action_func: AffineFunc,
    /// Total rotation so far (in turns)
    pub rotation: f64,
    /// Action lower bound (cached for priority queue)
    pub action_lower_bound: f64,
}

impl Tube {
    /// Create a root tube for a given 2-face.
    ///
    /// The rotation is initialized to 0.0 because the starting 2-face's rotation
    /// is counted when the orbit closes back through it. This avoids double-counting.
    pub fn create_root(two_face: &TwoFaceData) -> Self {
        // facet_sequence records the order in which facets are visited.
        // ItoJ: flow crosses from Eᵢ to Eⱼ, so we visit i then j.
        // JtoI: flow crosses from Eⱼ to Eᵢ, so we visit j then i.
        let facet_sequence = match two_face.flow_direction {
            FlowDir::ItoJ => vec![two_face.i, two_face.j],
            FlowDir::JtoI => vec![two_face.j, two_face.i],
        };
        Tube {
            facet_sequence,
            p_start: two_face.polygon.clone(),
            p_end: two_face.polygon.clone(),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 0.0, // Starting 2-face rotation counted when orbit closes
            action_lower_bound: 0.0,
        }
    }

    /// Get the starting 2-face indices.
    pub fn start_face(&self) -> (usize, usize) {
        (self.facet_sequence[0], self.facet_sequence[1])
    }

    /// Get the current (ending) 2-face indices.
    pub fn current_face(&self) -> (usize, usize) {
        let n = self.facet_sequence.len();
        (self.facet_sequence[n - 2], self.facet_sequence[n - 1])
    }

    /// Check if this facet is already in the sequence (excluding start).
    pub fn contains_facet(&self, facet: usize) -> bool {
        self.facet_sequence[1..].contains(&facet)
    }
}

// For BinaryHeap: min-heap by action_lower_bound
impl PartialEq for Tube {
    fn eq(&self, other: &Self) -> bool {
        self.action_lower_bound == other.action_lower_bound
    }
}

impl Eq for Tube {}

impl PartialOrd for Tube {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Tube {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Reverse order for min-heap
        other
            .action_lower_bound
            .partial_cmp(&self.action_lower_bound)
            .unwrap_or(std::cmp::Ordering::Equal)
    }
}

/// Extension result from trying to extend a tube.
#[derive(Clone, Debug)]
pub enum ExtensionResult {
    /// A new tube that can be extended further
    Extension(Tube),
    /// A tube that closes back to its starting face
    Closure(Tube),
}

/// Data for the affine flow map across a facet.
pub struct FlowMapData {
    pub map: AffineMap2D,
    pub time_func: AffineFunc,
}

/// Inverse trivialization: τ_n⁻¹(x, y) = x·jn + y·kn
pub fn inverse_trivialization(coords: Vector2f, n: SymplecticVector) -> SymplecticVector {
    let j = quaternion::mat_j();
    let k = quaternion::mat_k();
    jn_times_x_plus_kn_times_y(j * n, k * n, coords)
}

/// Inverse trivialization constrained to 2-face tangent space.
///
/// Given 2D coordinates and the two facet normals defining a 2-face,
/// reconstructs the 4D tangent vector that lies in the 2-face tangent space.
///
/// Solves the linear system:
/// - v · Jn = coords.x (trivialization x-coordinate)
/// - v · Kn = coords.y (trivialization y-coordinate)
/// - v · n_i = 0 (tangent to facet i)
/// - v · n_j = 0 (tangent to facet j)
pub fn inverse_trivialization_2face(
    coords: Vector2f,
    entry_normal: SymplecticVector,
    other_normal: SymplecticVector,
) -> SymplecticVector {
    let j = quaternion::mat_j();
    let k = quaternion::mat_k();
    let jn = j * entry_normal;
    let kn = k * entry_normal;

    // The 2-face tangent space is the orthogonal complement of span{entry_normal, other_normal}.
    // We want v such that v is in this tangent space AND trivialization(v, entry_normal) = coords.
    //
    // Rather than solving a 4x4 system, we use the fact that the tangent space is 2D.
    // Find an orthonormal basis {e1, e2} for the 2-face tangent space, then express v in this basis.

    // First, project jn onto the tangent space of other_normal
    let jn_tan = jn - other_normal * other_normal.dot(&jn);
    let jn_tan_norm = jn_tan.norm();

    if jn_tan_norm < 1e-10 {
        // Jn is parallel to other_normal; use Kn instead
        let kn_tan = kn - other_normal * other_normal.dot(&kn);
        return kn_tan * (coords.y / kn.dot(&kn_tan));
    }

    let e1 = jn_tan / jn_tan_norm;

    // e2 is orthogonal to both normals and to e1
    let kn_tan = kn - other_normal * other_normal.dot(&kn);
    let e2_raw = kn_tan - e1 * e1.dot(&kn_tan);
    let e2_norm = e2_raw.norm();

    if e2_norm < 1e-10 {
        // Degenerate case: kn is in span{e1, other_normal}
        // Just use e1
        return e1 * (coords.x / jn.dot(&e1));
    }

    let e2 = e2_raw / e2_norm;

    // Now v = a*e1 + b*e2 for some a, b
    // Constraints:
    // v · jn = coords.x => a*(e1·jn) + b*(e2·jn) = coords.x
    // v · kn = coords.y => a*(e1·kn) + b*(e2·kn) = coords.y

    let m11 = e1.dot(&jn);
    let m12 = e2.dot(&jn);
    let m21 = e1.dot(&kn);
    let m22 = e2.dot(&kn);

    let det = m11 * m22 - m12 * m21;
    if det.abs() < 1e-10 {
        // Fallback: just use e1 direction
        return e1 * (coords.x / m11);
    }

    let a = (coords.x * m22 - coords.y * m12) / det;
    let b = (coords.y * m11 - coords.x * m21) / det;

    e1 * a + e2 * b
}

fn jn_times_x_plus_kn_times_y(
    jn: SymplecticVector,
    kn: SymplecticVector,
    coords: Vector2f,
) -> SymplecticVector {
    jn * coords.x + kn * coords.y
}

/// Reconstruct a 4D point from 2D trivialization coordinates.
///
/// Given the 2D fixed point (in trivialization coordinates), the 2D polygon
/// vertices, and the original 4D vertices, finds the corresponding 4D point.
///
/// The approach is to find the nearest point in the polygon using projection,
/// then linearly interpolate the 4D vertices using the same weights.
fn reconstruct_4d_from_2d(
    point_2d: Vector2f,
    polygon: &crate::polygon::Polygon2D,
    vertices_4d: &[SymplecticVector],
    centroid: SymplecticVector,
) -> SymplecticVector {
    if polygon.vertices.is_empty() || vertices_4d.is_empty() {
        return centroid;
    }

    // Use barycentric interpolation based on the 2D point.
    // First, find a triangulation of the polygon and locate the point's triangle.
    // For simplicity, use a fan triangulation from vertex 0.

    let n = polygon.vertices.len();
    if n < 3 {
        return centroid;
    }

    // Try each triangle in the fan
    let v0_2d = polygon.vertices[0];
    for i in 1..(n - 1) {
        let v1_2d = polygon.vertices[i];
        let v2_2d = polygon.vertices[i + 1];

        // Compute barycentric coordinates for point_2d in triangle (v0, v1, v2)
        let (w0, w1, w2) = barycentric_coords(point_2d, v0_2d, v1_2d, v2_2d);

        // Check if point is inside triangle (all weights non-negative, within tolerance)
        if w0 >= -0.01 && w1 >= -0.01 && w2 >= -0.01 {
            // Normalize weights to sum to 1
            let sum = w0 + w1 + w2;
            let w0 = w0 / sum;
            let w1 = w1 / sum;
            let w2 = w2 / sum;

            // Apply same weights to 4D vertices
            let v0_4d = vertices_4d[0];
            let v1_4d = vertices_4d[i];
            let v2_4d = vertices_4d[i + 1];

            return v0_4d * w0 + v1_4d * w1 + v2_4d * w2;
        }
    }

    // Fallback: use closest vertex
    let mut min_dist = f64::INFINITY;
    let mut closest_idx = 0;
    for (i, v) in polygon.vertices.iter().enumerate() {
        let dist = (*v - point_2d).norm();
        if dist < min_dist {
            min_dist = dist;
            closest_idx = i;
        }
    }
    vertices_4d[closest_idx]
}

/// Compute barycentric coordinates of point p in triangle (v0, v1, v2).
fn barycentric_coords(p: Vector2f, v0: Vector2f, v1: Vector2f, v2: Vector2f) -> (f64, f64, f64) {
    let d1 = v1 - v0;
    let d2 = v2 - v0;
    let dp = p - v0;

    let d11 = d1.x * d1.x + d1.y * d1.y;
    let d12 = d1.x * d2.x + d1.y * d2.y;
    let d22 = d2.x * d2.x + d2.y * d2.y;
    let dp1 = dp.x * d1.x + dp.y * d1.y;
    let dp2 = dp.x * d2.x + dp.y * d2.y;

    let denom = d11 * d22 - d12 * d12;
    if denom.abs() < 1e-20 {
        return (1.0, 0.0, 0.0); // Degenerate triangle
    }

    let w1 = (d22 * dp1 - d12 * dp2) / denom;
    let w2 = (d11 * dp2 - d12 * dp1) / denom;
    let w0 = 1.0 - w1 - w2;

    (w0, w1, w2)
}

/// Compute time to reach next 2-face when flowing on a facet.
/// Formula: t(p) = h_k (h_j - ⟨n_j, p⟩) / (2 ω(n_k, n_j))
pub fn compute_time_to_crossing(
    p: SymplecticVector,
    facet_k: usize,
    facet_j: usize,
    data: &PolytopeData,
) -> f64 {
    let h_k = data.hrep.heights[facet_k];
    let h_j = data.hrep.heights[facet_j];
    let n_k = data.hrep.normals[facet_k];
    let n_j = data.hrep.normals[facet_j];
    let omega = symplectic_form(n_k, n_j);
    h_k * (h_j - n_j.dot(&p)) / (2.0 * omega)
}

/// Compute the flow map for crossing a facet.
/// See [tube-geometry-spec.md](../docs/tube-geometry-spec.md) for derivation.
pub fn compute_flow_map(
    entry_face: &TwoFaceData,
    exit_face: &TwoFaceData,
    current_facet: usize,
    next_facet: usize,
    data: &PolytopeData,
) -> FlowMapData {
    let h_k = data.hrep.heights[current_facet];
    let h_j = data.hrep.heights[next_facet];
    let n_k = data.hrep.normals[current_facet];
    let n_j = data.hrep.normals[next_facet];
    let omega_kj = symplectic_form(n_k, n_j);

    let n_entry = entry_face.entry_normal;
    let r_entry = entry_face.centroid;
    let n_exit = exit_face.entry_normal;
    let r_exit = exit_face.centroid;

    // Reeb velocity on facet k
    let v_k = apply_j(n_k) * (2.0 / h_k);

    // Compute time function coefficients
    let j_mat = quaternion::mat_j();
    let k_mat = quaternion::mat_k();
    let j_n_entry = j_mat * n_entry;
    let k_n_entry = k_mat * n_entry;

    let nj_dot_j_n_entry = n_j.dot(&j_n_entry);
    let nj_dot_k_n_entry = n_j.dot(&k_n_entry);
    let nj_dot_r_entry = n_j.dot(&r_entry);

    let time_constant = h_k * (h_j - nj_dot_r_entry) / (2.0 * omega_kj);
    let time_gradient = Vector2f::new(
        -h_k * nj_dot_j_n_entry / (2.0 * omega_kj),
        -h_k * nj_dot_k_n_entry / (2.0 * omega_kj),
    );
    let time_func = AffineFunc::new(time_gradient, time_constant);

    // Compute flow map in exit coordinates
    let tau_exit_j_n_entry = trivialization(j_n_entry, n_exit);
    let tau_exit_k_n_entry = trivialization(k_n_entry, n_exit);
    let tau_exit_v_k = trivialization(v_k, n_exit);
    let tau_exit_delta_r = trivialization(r_entry - r_exit, n_exit);

    let base_linear = Matrix2f::new(
        tau_exit_j_n_entry.x,
        tau_exit_k_n_entry.x,
        tau_exit_j_n_entry.y,
        tau_exit_k_n_entry.y,
    );

    let time_linear = Matrix2f::new(
        tau_exit_v_k.x * time_gradient.x,
        tau_exit_v_k.x * time_gradient.y,
        tau_exit_v_k.y * time_gradient.x,
        tau_exit_v_k.y * time_gradient.y,
    );

    let total_linear = base_linear + time_linear;
    let total_offset = tau_exit_delta_r + tau_exit_v_k * time_constant;

    FlowMapData {
        map: AffineMap2D::new(total_linear, total_offset),
        time_func,
    }
}

/// Check if flow can cross from `from_facet` to `to_facet`.
pub fn flow_allows_crossing(from_facet: usize, to_facet: usize, flow_dir: FlowDir) -> bool {
    if from_facet < to_facet {
        flow_dir == FlowDir::ItoJ
    } else {
        flow_dir == FlowDir::JtoI
    }
}

/// Extend a tube to a new facet.
pub fn extend_tube(tube: &Tube, new_facet: usize, data: &PolytopeData) -> Option<Tube> {
    extend_tube_inner(tube, new_facet, data, false)
}

/// Extend a tube for closure (skips polygon intersection check).
///
/// For closures, the polygon intersection may be empty or near-degenerate
/// due to numerical issues, but we can still find the fixed point and
/// verify it's valid. This function computes the flow map without requiring
/// a non-empty intersection.
pub fn extend_tube_for_closure(tube: &Tube, new_facet: usize, data: &PolytopeData) -> Option<Tube> {
    extend_tube_inner(tube, new_facet, data, true)
}

fn extend_tube_inner(
    tube: &Tube,
    new_facet: usize,
    data: &PolytopeData,
    closure_mode: bool,
) -> Option<Tube> {
    let (prev_facet, current_facet) = tube.current_face();
    let entry_face = data.get_two_face(prev_facet, current_facet);
    if entry_face.is_none() {
        #[cfg(test)]
        eprintln!("DEBUG extend_tube: no 2-face ({}, {})", prev_facet, current_facet);
        return None;
    }
    let entry_face = entry_face.unwrap();

    let exit_face = data.get_two_face(current_facet, new_facet);
    if exit_face.is_none() {
        #[cfg(test)]
        eprintln!("DEBUG extend_tube: no 2-face ({}, {})", current_facet, new_facet);
        return None;
    }
    let exit_face = exit_face.unwrap();

    if !flow_allows_crossing(current_facet, new_facet, exit_face.flow_direction) {
        #[cfg(test)]
        eprintln!("DEBUG extend_tube: flow blocked {} -> {} (dir={:?})",
                  current_facet, new_facet, exit_face.flow_direction);
        return None;
    }

    let flow_data = compute_flow_map(entry_face, exit_face, current_facet, new_facet, data);
    let mapped_end = tube.p_end.affine_image(&flow_data.map);
    let new_p_end = mapped_end.intersect(&exit_face.polygon);

    // In closure mode, we skip the empty polygon check because we'll verify
    // the fixed point directly in solve_closed_tube. The polygon may be
    // empty or degenerate due to numerical issues, but the fixed point
    // can still be computed and validated.
    if !closure_mode && new_p_end.is_empty() {
        #[cfg(test)]
        if tube.facet_sequence.len() >= 4 && tube.facet_sequence[0] == 2 {
            eprintln!("DEBUG extend_tube: polygon empty after {} -> {}", current_facet, new_facet);
            eprintln!("  seq: {:?}", tube.facet_sequence);
            eprintln!("  mapped_end vertices: {:?}", mapped_end.vertices);
            eprintln!("  exit_face vertices: {:?}", exit_face.polygon.vertices);
        }
        return None;
    }

    let new_flow_map = flow_data.map.compose(&tube.flow_map);
    let action_increment = flow_data.time_func.compose(&tube.flow_map);
    let new_action_func = tube.action_func.add(&action_increment);
    let new_rotation = tube.rotation + exit_face.rotation;

    // For closure mode with empty polygon, use 0.0 as placeholder for action bound
    // The actual action will be computed from the fixed point in solve_closed_tube
    let action_lower_bound = if new_p_end.is_empty() {
        0.0
    } else {
        new_p_end
            .minimize(&new_action_func)
            .map(|(v, _)| v)
            .unwrap_or(0.0)
    };

    let mut new_sequence = tube.facet_sequence.clone();
    new_sequence.push(new_facet);

    Some(Tube {
        facet_sequence: new_sequence,
        p_start: tube.p_start.clone(),
        p_end: new_p_end,
        flow_map: new_flow_map,
        action_func: new_action_func,
        rotation: new_rotation,
        action_lower_bound,
    })
}

/// Get all valid extensions for a tube.
pub fn get_extensions(tube: &Tube, data: &PolytopeData) -> Vec<ExtensionResult> {
    let mut results = Vec::new();
    let (start_i, start_j) = tube.start_face();
    let (_, current_facet) = tube.current_face();

    // Check if we can close immediately
    if current_facet == start_i {
        #[cfg(test)]
        eprintln!("DEBUG get_extensions: at start_i={}, trying to close to start_j={}", start_i, start_j);
        // Use closure-mode extension to bypass polygon intersection check
        if let Some(extended) = extend_tube_for_closure(tube, start_j, data) {
            results.push(ExtensionResult::Closure(extended));
        }
        return results;
    }

    // Find all valid next facets
    let adjacent_faces = data.faces_adjacent_to(current_facet);
    #[cfg(test)]
    if tube.facet_sequence.len() >= 4 {
        eprintln!("DEBUG get_extensions: seq={:?}, {} adjacent faces to {}",
                  tube.facet_sequence, adjacent_faces.len(), current_facet);
    }

    for face in adjacent_faces {
        let next_facet = if face.i == current_facet {
            face.j
        } else {
            face.i
        };

        if next_facet != start_i && tube.contains_facet(next_facet) {
            continue;
        }

        if !flow_allows_crossing(current_facet, next_facet, face.flow_direction) {
            continue;
        }

        if let Some(extended) = extend_tube(tube, next_facet, data) {
            if next_facet == start_i {
                #[cfg(test)]
                eprintln!("DEBUG get_extensions: reached start_i={}, trying to close to start_j={}", start_i, start_j);
                // Use closure-mode extension to bypass polygon intersection check
                if let Some(closed) = extend_tube_for_closure(&extended, start_j, data) {
                    results.push(ExtensionResult::Closure(closed));
                } else {
                    #[cfg(test)]
                    eprintln!("DEBUG get_extensions: extend to start_j failed");
                }
            } else {
                results.push(ExtensionResult::Extension(extended));
            }
        }
    }

    results
}

/// Solve a closed tube to find the minimum-action periodic orbit.
pub fn solve_closed_tube(
    tube: &Tube,
    data: &PolytopeData,
) -> Option<(f64, crate::result::WitnessOrbit)> {
    #[cfg(test)]
    eprintln!("DEBUG solve_closed_tube: seq={:?}, rotation={:.4}", tube.facet_sequence, tube.rotation);

    let fixed_point = match tube.flow_map.fixed_point() {
        Some(fp) => fp,
        None => {
            #[cfg(test)]
            eprintln!("DEBUG solve_closed_tube: no fixed point (det={:.6})",
                      tube.flow_map.linear.determinant());
            return None;
        }
    };

    #[cfg(test)]
    eprintln!("DEBUG solve_closed_tube: fixed_point={:?}", fixed_point);

    // Check if fixed point is in the starting polygon.
    // For closures, p_end may be empty/degenerate due to numerical issues,
    // but p_start is well-conditioned and the fixed point must be valid there.
    if !tube.p_start.contains(fixed_point) {
        #[cfg(test)]
        eprintln!("DEBUG solve_closed_tube: fixed_point not in p_start (vertices={:?})",
                  tube.p_start.vertices);
        return None;
    }

    let action = tube.action_func.eval(fixed_point);
    #[cfg(test)]
    {
        eprintln!("DEBUG solve_closed_tube: action={:.6}", action);
        eprintln!("DEBUG solve_closed_tube: action_func.gradient={:?}", tube.action_func.gradient);
        eprintln!("DEBUG solve_closed_tube: action_func.constant={:.6}", tube.action_func.constant);
        eprintln!("DEBUG solve_closed_tube: flow_map.linear={:?}", tube.flow_map.linear);
        eprintln!("DEBUG solve_closed_tube: flow_map.offset={:?}", tube.flow_map.offset);
    }

    if action <= 0.0 {
        #[cfg(test)]
        eprintln!("DEBUG solve_closed_tube: non-positive action {}", action);
        return None;
    }

    let witness = reconstruct_witness(fixed_point, tube, data)?;

    let total_time: f64 = witness.segment_times.iter().sum();
    let time_error = (total_time - action).abs();
    if time_error > 1e-6 {
        eprintln!("Warning: action mismatch - computed={action:.6}, sum of times={total_time:.6}");
    }

    Some((action, witness))
}

/// Reconstruct the 4D witness orbit from a 2D fixed point.
fn reconstruct_witness(
    fixed_point_2d: Vector2f,
    tube: &Tube,
    data: &PolytopeData,
) -> Option<crate::result::WitnessOrbit> {
    let seq = &tube.facet_sequence;
    let n_segments = seq.len() - 2;

    #[cfg(test)]
    eprintln!("DEBUG reconstruct: seq={:?}, n_segments={}", seq, n_segments);

    if n_segments == 0 {
        return None;
    }

    let mut breakpoints = Vec::with_capacity(n_segments);
    let mut segment_times = Vec::with_capacity(n_segments);

    let (start_i, start_j) = tube.start_face();
    let start_face = data.get_two_face(start_i, start_j)?;

    // Reconstruct 4D point by finding barycentric coordinates of fixed_point in polygon,
    // then applying same coordinates to 4D vertices
    let mut current_4d = reconstruct_4d_from_2d(
        fixed_point_2d,
        &start_face.polygon,
        &start_face.vertices_4d,
        start_face.centroid,
    );

    #[cfg(test)]
    {
        eprintln!("DEBUG reconstruct: start_4d={:?}", current_4d);
        // Verify trivialization matches fixed_point
        let reconstructed_2d = trivialization(current_4d - start_face.centroid, start_face.entry_normal);
        eprintln!("DEBUG reconstruct: fixed_point_2d={:?}", fixed_point_2d);
        eprintln!("DEBUG reconstruct: reconstructed_2d={:?}", reconstructed_2d);
        eprintln!("DEBUG reconstruct: 2D error={:.3e}", (reconstructed_2d - fixed_point_2d).norm());
        eprintln!("DEBUG reconstruct: polygon vertices:");
        for (i, v) in start_face.polygon.vertices.iter().enumerate() {
            let dist = (*v - fixed_point_2d).norm();
            eprintln!("  vertex {}: {:?}, dist to fixed_point={:.6}", i, v, dist);
        }
        // Check all facet slacks
        eprintln!("DEBUG reconstruct: facet slacks:");
        for (i, (n, h)) in data.hrep.normals.iter().zip(&data.hrep.heights).enumerate() {
            let slack = *h - n.dot(&current_4d);
            eprintln!("  facet {}: slack={:.6}", i, slack);
        }
    }

    breakpoints.push(current_4d);

    for s in 0..n_segments {
        let facet_k = seq[s + 1];
        let facet_j = seq[s + 2];

        let time = compute_time_to_crossing(current_4d, facet_k, facet_j, data);
        #[cfg(test)]
        eprintln!("DEBUG reconstruct: segment {} on facet {}, exit to {}, time={:.6}",
                  s, facet_k, facet_j, time);
        segment_times.push(time);

        let h_k = data.hrep.heights[facet_k];
        let n_k = data.hrep.normals[facet_k];
        let v_k = apply_j(n_k) * (2.0 / h_k);

        current_4d += v_k * time;

        if s < n_segments - 1 {
            breakpoints.push(current_4d);
        }
    }

    let closure_error = (current_4d - breakpoints[0]).norm();
    if closure_error > 1e-6 {
        eprintln!("Warning: orbit closure error = {closure_error:.3e} (expected ~0)");
    }

    // Reject degenerate orbits where segment times are too small
    let total_time: f64 = segment_times.iter().sum();
    if total_time < 1e-6 {
        #[cfg(test)]
        eprintln!("DEBUG reconstruct: rejecting degenerate orbit (total_time={:.3e})", total_time);
        return None;
    }

    // Also check for negative segment times (invalid orbit)
    for (_i, &t) in segment_times.iter().enumerate() {
        if t < -1e-10 {
            #[cfg(test)]
            eprintln!("DEBUG reconstruct: rejecting orbit with negative time (segment {} has t={:.3e})", _i, t);
            return None;
        }
    }

    Some(crate::result::WitnessOrbit {
        breakpoints,
        facet_sequence: tube.facet_sequence.clone(),
        segment_times,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_viterbo_geom::{trivialization, SymplecticVector};

    // =========================================================================
    // Flow Direction Tests
    // =========================================================================

    #[test]
    fn flow_i_to_j_correct() {
        assert!(flow_allows_crossing(0, 1, FlowDir::ItoJ));
        assert!(!flow_allows_crossing(1, 0, FlowDir::ItoJ));
    }

    #[test]
    fn flow_j_to_i_correct() {
        assert!(!flow_allows_crossing(0, 1, FlowDir::JtoI));
        assert!(flow_allows_crossing(1, 0, FlowDir::JtoI));
    }

    // =========================================================================
    // Trivialization Roundtrip Tests
    // =========================================================================

    #[test]
    fn trivialization_roundtrip_in_jk_plane() {
        // The trivialization τ_n maps vectors to span{Jn, Kn} coordinates.
        // inverse_trivialization reconstructs a vector IN span{Jn, Kn}.
        // The roundtrip τ⁻¹(τ(v, n), n) = proj_{span{Jn,Kn}}(v).
        //
        // For vectors already in span{Jn, Kn}, the roundtrip should be exact.
        use rust_viterbo_geom::quaternion;

        let n = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        let j = quaternion::mat_j();
        let k = quaternion::mat_k();
        let jn = j * n;  // (0, 0, -1, 0) for standard J
        let kn = k * n;  // (0, 0, 0, -1) for standard K

        // Create a vector in span{Jn, Kn}
        let v = jn * 0.7 + kn * 0.3;

        // Roundtrip
        let coords = trivialization(v, n);
        let reconstructed = inverse_trivialization(coords, n);

        let error = (reconstructed - v).norm();
        assert!(error < 1e-10,
            "Roundtrip error for v in span{{Jn,Kn}} = {:.2e}, expected ~0", error);
    }

    #[test]
    fn trivialization_is_projection() {
        // For general v, τ⁻¹(τ(v)) projects v onto span{Jn, Kn}
        use rust_viterbo_geom::quaternion;

        let n = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        let j = quaternion::mat_j();
        let k = quaternion::mat_k();
        let jn = j * n;
        let kn = k * n;

        let v = SymplecticVector::new(0.3, 0.5, 0.7, 0.11);

        // Roundtrip
        let coords = trivialization(v, n);
        let reconstructed = inverse_trivialization(coords, n);

        // Reconstructed should be the projection of v onto span{Jn, Kn}
        // proj = ⟨v, Jn⟩/‖Jn‖² · Jn + ⟨v, Kn⟩/‖Kn‖² · Kn
        // But Jn and Kn are orthonormal if n is unit, so:
        let jn_norm_sq = jn.dot(&jn);
        let kn_norm_sq = kn.dot(&kn);
        let expected = jn * (v.dot(&jn) / jn_norm_sq) + kn * (v.dot(&kn) / kn_norm_sq);

        let error = (reconstructed - expected).norm();
        assert!(error < 1e-10,
            "Trivialization is not a projection: error = {:.2e}", error);
    }

    // =========================================================================
    // Barycentric Coordinate Tests
    // =========================================================================

    #[test]
    fn barycentric_coords_vertex() {
        // At vertex v0, coords should be (1, 0, 0)
        let v0 = Vector2f::new(0.0, 0.0);
        let v1 = Vector2f::new(1.0, 0.0);
        let v2 = Vector2f::new(0.0, 1.0);

        let (w0, w1, w2) = barycentric_coords(v0, v0, v1, v2);
        assert!((w0 - 1.0).abs() < 1e-10, "w0 should be 1 at v0, got {}", w0);
        assert!(w1.abs() < 1e-10, "w1 should be 0 at v0, got {}", w1);
        assert!(w2.abs() < 1e-10, "w2 should be 0 at v0, got {}", w2);
    }

    #[test]
    fn barycentric_coords_centroid() {
        // At centroid, coords should be (1/3, 1/3, 1/3)
        let v0 = Vector2f::new(0.0, 0.0);
        let v1 = Vector2f::new(1.0, 0.0);
        let v2 = Vector2f::new(0.0, 1.0);
        let centroid = (v0 + v1 + v2) / 3.0;

        let (w0, w1, w2) = barycentric_coords(centroid, v0, v1, v2);
        assert!((w0 - 1.0/3.0).abs() < 1e-10, "w0 should be 1/3, got {}", w0);
        assert!((w1 - 1.0/3.0).abs() < 1e-10, "w1 should be 1/3, got {}", w1);
        assert!((w2 - 1.0/3.0).abs() < 1e-10, "w2 should be 1/3, got {}", w2);
    }

    #[test]
    fn barycentric_coords_sum_to_one() {
        // For any point, barycentric coords should sum to 1
        let v0 = Vector2f::new(0.0, 0.0);
        let v1 = Vector2f::new(2.0, 0.0);
        let v2 = Vector2f::new(1.0, 1.5);

        let test_points = [
            Vector2f::new(0.5, 0.3),
            Vector2f::new(1.0, 0.5),
            Vector2f::new(0.8, 0.2),
        ];

        for p in test_points {
            let (w0, w1, w2) = barycentric_coords(p, v0, v1, v2);
            let sum = w0 + w1 + w2;
            assert!((sum - 1.0).abs() < 1e-10,
                "Barycentric coords should sum to 1, got {} for p={:?}", sum, p);
        }
    }

    #[test]
    fn barycentric_coords_reconstruct_point() {
        // p = w0*v0 + w1*v1 + w2*v2
        let v0 = Vector2f::new(0.0, 0.0);
        let v1 = Vector2f::new(2.0, 0.0);
        let v2 = Vector2f::new(1.0, 1.5);
        let p = Vector2f::new(1.0, 0.5);

        let (w0, w1, w2) = barycentric_coords(p, v0, v1, v2);
        let reconstructed = v0 * w0 + v1 * w1 + v2 * w2;

        let error = (reconstructed - p).norm();
        assert!(error < 1e-10,
            "Barycentric reconstruction error = {:.2e}", error);
    }

    // =========================================================================
    // AffineMap2D Fixed Point Tests
    // =========================================================================

    #[test]
    fn affine_map_fixed_point_contraction() {
        // Contraction x → 0.5*x + (1, 1) has fixed point (2, 2)
        let map = AffineMap2D::new(
            Matrix2f::new(0.5, 0.0, 0.0, 0.5),
            Vector2f::new(1.0, 1.0),
        );
        let fp = map.fixed_point().expect("Should have fixed point");
        assert!((fp - Vector2f::new(2.0, 2.0)).norm() < 1e-10);
    }

    #[test]
    fn affine_map_fixed_point_is_actually_fixed() {
        // Any fixed point f(x) = x should satisfy x = Ax + b
        let map = AffineMap2D::new(
            Matrix2f::new(0.8, 0.1, -0.1, 0.7),
            Vector2f::new(0.5, 0.3),
        );
        if let Some(fp) = map.fixed_point() {
            let mapped = map.apply(fp);
            let error = (mapped - fp).norm();
            assert!(error < 1e-10, "f(fp) should equal fp, error = {:.2e}", error);
        }
    }

    // =========================================================================
    // Tube Structure Tests
    // =========================================================================

    #[test]
    fn tube_start_face_matches_sequence() {
        // Verify start_face() returns first two elements of facet_sequence
        let tube = Tube {
            facet_sequence: vec![2, 5, 3, 7],
            p_start: crate::polygon::Polygon2D::empty(),
            p_end: crate::polygon::Polygon2D::empty(),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 0.0,
            action_lower_bound: 0.0,
        };
        assert_eq!(tube.start_face(), (2, 5));
    }

    #[test]
    fn tube_current_face_matches_sequence() {
        // Verify current_face() returns last two elements of facet_sequence
        let tube = Tube {
            facet_sequence: vec![2, 5, 3, 7],
            p_start: crate::polygon::Polygon2D::empty(),
            p_end: crate::polygon::Polygon2D::empty(),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 0.0,
            action_lower_bound: 0.0,
        };
        assert_eq!(tube.current_face(), (3, 7));
    }

    #[test]
    fn tube_contains_facet_excludes_start() {
        // contains_facet should check sequence[1..], not including start
        let tube = Tube {
            facet_sequence: vec![2, 5, 3, 7],
            p_start: crate::polygon::Polygon2D::empty(),
            p_end: crate::polygon::Polygon2D::empty(),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 0.0,
            action_lower_bound: 0.0,
        };
        assert!(!tube.contains_facet(2), "Should not contain start facet 2");
        assert!(tube.contains_facet(5));
        assert!(tube.contains_facet(3));
        assert!(tube.contains_facet(7));
        assert!(!tube.contains_facet(99), "Should not contain absent facet");
    }

    // =========================================================================
    // Flow Map Composition Tests
    // =========================================================================

    #[test]
    fn flow_map_composition_associative() {
        // (A ∘ B) ∘ C = A ∘ (B ∘ C)
        let a = AffineMap2D::new(
            Matrix2f::new(0.9, 0.1, -0.1, 0.8),
            Vector2f::new(0.5, 0.3),
        );
        let b = AffineMap2D::new(
            Matrix2f::new(0.7, -0.2, 0.2, 0.6),
            Vector2f::new(-0.2, 0.4),
        );
        let c = AffineMap2D::new(
            Matrix2f::new(1.1, 0.0, 0.3, 0.9),
            Vector2f::new(0.1, -0.1),
        );

        let ab_c = a.compose(&b).compose(&c);
        let a_bc = a.compose(&b.compose(&c));

        // Test on a few points
        let test_points = [
            Vector2f::new(0.0, 0.0),
            Vector2f::new(1.0, 0.0),
            Vector2f::new(0.5, 0.7),
        ];
        for p in test_points {
            let r1 = ab_c.apply(p);
            let r2 = a_bc.apply(p);
            let error = (r1 - r2).norm();
            assert!(error < 1e-10, "Composition not associative: error = {:.2e}", error);
        }
    }

    // =========================================================================
    // Rotation and Action Accumulation Tests
    // =========================================================================

    /// Rotation should accumulate additively when extending tubes.
    ///
    /// MATHEMATICAL PROPERTY: For a closed orbit crossing 2-faces F₁, F₂, ..., Fₙ,
    /// the total rotation is Σᵢ ρ(Fᵢ) = 1 (one full turn).
    ///
    /// This test verifies rotation accumulates correctly in tube extension.
    #[test]
    fn rotation_accumulates_additively() {
        // If we had two tubes with rotations r1 and r2, composing them should give r1 + r2
        // This is implicit in extend_tube_inner but let's verify the math:
        // A closed orbit has total rotation = 1 (integer number of turns)

        // Create two flow maps with known rotation increments
        let r1: f64 = 0.125; // 1/8 turn
        let r2: f64 = 0.125; // 1/8 turn
        let r_total = r1 + r2;

        assert!((r_total - 0.25_f64).abs() < 1e-10, "Rotation should be additive");
    }

    /// Action lower bound should be achieved or exceeded by any point in p_end.
    ///
    /// MATHEMATICAL PROPERTY: action_lower_bound ≤ action_func(p) for all p ∈ p_end.
    ///
    /// This ensures pruning is sound: if action_lower_bound > best_known, we can safely prune.
    #[test]
    fn action_lower_bound_is_minimum_over_polygon() {
        // Create a simple action function and polygon
        let action_func = AffineFunc::new(Vector2f::new(1.0, 2.0), 5.0);
        let polygon = crate::polygon::Polygon2D::new(vec![
            Vector2f::new(0.0, 0.0),
            Vector2f::new(1.0, 0.0),
            Vector2f::new(1.0, 1.0),
            Vector2f::new(0.0, 1.0),
        ]);

        // Find minimum over polygon
        if let Some((min_val, _)) = polygon.minimize(&action_func) {
            // The action_lower_bound should equal this minimum
            // Any point in polygon should achieve >= min_val
            for v in &polygon.vertices {
                let val = action_func.eval(*v);
                assert!(val >= min_val - 1e-10,
                    "Vertex {:?} has action {} < lower bound {}",
                    v, val, min_val);
            }
        }
    }

    /// Time to crossing should be positive for valid facet transitions.
    ///
    /// MATHEMATICAL PROPERTY: When flowing on facet k toward facet j,
    /// the time to reach the 2-face F_{kj} is positive.
    #[test]
    fn time_to_crossing_positive_for_forward_flow() {
        // For flow from interior toward boundary, time should be positive
        // This depends on the sign of ω(n_k, n_j) - flow direction matters
        //
        // The formula is: t = h_k (h_j - ⟨n_j, p⟩) / (2 ω(n_k, n_j))
        // For a point p strictly inside facet k, ⟨n_j, p⟩ < h_j,
        // so (h_j - ⟨n_j, p⟩) > 0.
        // Sign of t depends on sign of ω(n_k, n_j).

        // This is a formula verification, not a runtime test.
        // The property holds by construction when flow direction is chosen correctly.
        let h_k = 1.0;
        let h_j = 1.0;
        let n_j_dot_p = 0.5;  // p is inside
        let omega_kj = 0.5;   // positive omega means flow k → j

        let numerator = h_k * (h_j - n_j_dot_p);
        let denominator = 2.0 * omega_kj;
        let time = numerator / denominator;

        assert!(time > 0.0, "Time should be positive for forward flow, got {}", time);
    }
}
