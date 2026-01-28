//! Volume computation for 4D convex polytopes.
//!
//! Given an H-representation (halfspace intersection), we:
//! 1. Convert H-rep to V-rep by computing vertices (intersection points of facets)
//! 2. Use QHull to compute the volume of the convex hull of these vertices
//!
//! # Algorithm
//!
//! For a polytope K = {x ∈ R⁴ : ⟨n_i, x⟩ ≤ h_i for all i}, we use a simplified
//! approach: compute convex hull from bounding box vertices and use QHull's volume.
//!
//! This is a placeholder implementation that computes volume from a bounding box.
//! A full implementation would enumerate all vertices of the polytope.

use nalgebra::Vector4;
use qhull::Qh;
use thiserror::Error;

/// Compute the volume of a 4D convex polytope from its H-representation.
///
/// # Arguments
///
/// - `normals`: Unit outward normals to each facet
/// - `heights`: Signed distances from origin to each facet (must be > 0)
///
/// # Returns
///
/// The volume in R⁴, or an error if the computation fails.
///
/// # Note
///
/// This implementation computes vertices by finding intersections of facets,
/// then uses QHull to compute the convex hull volume.
///
/// # Example
///
/// ```
/// use geom::volume::polytope_volume_hrep;
/// use nalgebra::Vector4;
///
/// // Tesseract [-1, 1]⁴ has volume 2⁴ = 16
/// let normals = vec![
///     Vector4::new( 1.0,  0.0,  0.0,  0.0),
///     Vector4::new(-1.0,  0.0,  0.0,  0.0),
///     Vector4::new( 0.0,  1.0,  0.0,  0.0),
///     Vector4::new( 0.0, -1.0,  0.0,  0.0),
///     Vector4::new( 0.0,  0.0,  1.0,  0.0),
///     Vector4::new( 0.0,  0.0, -1.0,  0.0),
///     Vector4::new( 0.0,  0.0,  0.0,  1.0),
///     Vector4::new( 0.0,  0.0,  0.0, -1.0),
/// ];
/// let heights = vec![1.0; 8];
///
/// let volume = polytope_volume_hrep(&normals, &heights).unwrap();
/// assert!((volume - 16.0).abs() < 1e-6);
/// ```
pub fn polytope_volume_hrep(normals: &[Vector4<f64>], heights: &[f64]) -> Result<f64, VolumeError> {
    if normals.len() != heights.len() {
        return Err(VolumeError::DimensionMismatch {
            normals: normals.len(),
            heights: heights.len(),
        });
    }

    if normals.is_empty() {
        return Err(VolumeError::EmptyInput);
    }

    // Compute vertices by enumerating all 4-subsets of facets and solving
    // the system of 4 linear equations. Each vertex is at the intersection
    // of exactly 4 facets in 4D.
    let vertices = compute_vertices(normals, heights)?;

    if vertices.is_empty() {
        return Err(VolumeError::NoVertices);
    }

    // Flatten vertices for QHull
    let mut points: Vec<f64> = vertices
        .iter()
        .flat_map(|v| vec![v[0], v[1], v[2], v[3]])
        .collect();

    // Compute convex hull with triangulated output
    // Qt option forces triangulated output (all facets are simplices)
    let qh = Qh::builder()
        .compute(true)
        .qhull_args(["Qt"]) // Triangulated output
        .map_err(|e| VolumeError::QHullError(format!("{:?}", e)))?
        .build(4, &mut points)
        .map_err(|e| VolumeError::QHullError(format!("{:?}", e)))?;

    // Compute volume from simplices
    let volume = compute_hull_volume(&qh, &vertices)?;

    if volume < 0.0 {
        return Err(VolumeError::NegativeVolume(volume));
    }

    Ok(volume)
}

/// Compute the volume of a convex hull from triangulated facets.
///
/// With Qt option, all facets are simplices (4 vertices in 4D).
/// We decompose into pyramids from origin to each facet.
fn compute_hull_volume(qh: &Qh, vertices: &[Vector4<f64>]) -> Result<f64, VolumeError> {
    // Use origin as apex point (it's guaranteed to be interior)
    let apex = Vector4::zeros();

    let mut total_volume = 0.0;

    // Iterate over all facets of the hull (all are simplices due to Qt option)
    for facet in qh.facets() {
        // Get vertex indices for this facet
        let facet_vertices = match facet.vertices() {
            Some(v) => v,
            None => continue,
        };

        let vertex_indices: Vec<usize> =
            facet_vertices.iter().filter_map(|v| v.index(qh)).collect();

        // Each facet should be a 3-simplex (4 vertices) due to Qt triangulation
        if vertex_indices.len() != 4 {
            continue;
        }

        // Form a 4-simplex [apex, v0, v1, v2, v3]
        let v0 = vertices[vertex_indices[0]];
        let v1 = vertices[vertex_indices[1]];
        let v2 = vertices[vertex_indices[2]];
        let v3 = vertices[vertex_indices[3]];

        let mat5 = Matrix5::from_rows(&[
            [apex[0], apex[1], apex[2], apex[3], 1.0].into(),
            [v0[0], v0[1], v0[2], v0[3], 1.0].into(),
            [v1[0], v1[1], v1[2], v1[3], 1.0].into(),
            [v2[0], v2[1], v2[2], v2[3], 1.0].into(),
            [v3[0], v3[1], v3[2], v3[3], 1.0].into(),
        ]);

        let pyramid_volume = mat5.determinant().abs() / 24.0;
        total_volume += pyramid_volume;
    }

    Ok(total_volume)
}

use nalgebra::Matrix5;

/// Compute vertices of a polytope from its H-representation.
///
/// Each vertex is the intersection of exactly 4 facets (in 4D).
/// We enumerate all 4-subsets and solve the linear system.
fn compute_vertices(
    normals: &[Vector4<f64>],
    heights: &[f64],
) -> Result<Vec<Vector4<f64>>, VolumeError> {
    use nalgebra::Matrix4;

    let n = normals.len();
    let mut vertices = Vec::new();

    // Enumerate all 4-subsets of facets
    for i in 0..n {
        for j in (i + 1)..n {
            for k in (j + 1)..n {
                for l in (k + 1)..n {
                    // Solve the system: N * x = h where N is 4x4 matrix of normals
                    let mat = Matrix4::from_rows(&[
                        normals[i].transpose(),
                        normals[j].transpose(),
                        normals[k].transpose(),
                        normals[l].transpose(),
                    ]);

                    let rhs = Vector4::new(heights[i], heights[j], heights[k], heights[l]);

                    // Solve N * x = h
                    if let Some(vertex) = mat.try_inverse().map(|inv| inv * rhs) {
                        // Check if this vertex satisfies all inequalities
                        let is_valid = normals
                            .iter()
                            .zip(heights.iter())
                            .all(|(n, &h)| n.dot(&vertex) <= h + 1e-6);

                        if is_valid {
                            // Check if not already in list (within tolerance)
                            let is_duplicate = vertices
                                .iter()
                                .any(|v: &Vector4<f64>| (v - vertex).norm() < 1e-6);

                            if !is_duplicate {
                                vertices.push(vertex);
                            }
                        }
                    }
                }
            }
        }
    }

    Ok(vertices)
}

/// Errors that can occur during volume computation.
#[derive(Debug, Error)]
pub enum VolumeError {
    /// Number of normals doesn't match number of heights.
    #[error("dimension mismatch: {normals} normals vs {heights} heights")]
    DimensionMismatch { normals: usize, heights: usize },

    /// Empty input arrays.
    #[error("empty input: need at least one halfspace")]
    EmptyInput,

    /// No vertices could be computed from the H-representation.
    #[error("no vertices found (polytope may be degenerate or unbounded)")]
    NoVertices,

    /// QHull computation failed.
    #[error("QHull error: {0}")]
    QHullError(String),

    /// Computed volume is negative (should be impossible).
    #[error("negative volume: {0}")]
    NegativeVolume(f64),
}

#[cfg(test)]
mod tests {
    use super::*;

    const TOL: f64 = 1e-6;

    /// Create a tesseract [-1, 1]⁴
    fn make_tesseract() -> (Vec<Vector4<f64>>, Vec<f64>) {
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, -1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, -1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(0.0, 0.0, 0.0, -1.0),
        ];
        let heights = vec![1.0; 8];
        (normals, heights)
    }

    /// Create a 4-simplex with vertices at origin and standard basis vectors
    fn make_4_simplex() -> (Vec<Vector4<f64>>, Vec<f64>) {
        // Vertices: (0,0,0,0), e1, e2, e3, e4
        // This is the convex hull of {0, e_i}
        // Volume = 1/4! = 1/24 ≈ 0.04166667

        // For H-representation, we need the facets.
        // The 5 facets are:
        // 1. The hyperplane through e1, e2, e3, e4 (opposite to origin)
        // 2-5. The 4 coordinate hyperplanes

        let normals = vec![
            // Facet opposite to origin: normal points outward
            // The hyperplane x1 + x2 + x3 + x4 = 1
            Vector4::new(0.5, 0.5, 0.5, 0.5), // Normalized
            // Four coordinate planes (x_i = 0), normals point in -e_i direction
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, -1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, -1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, -1.0),
        ];

        // Heights: distance from origin to each facet
        // For x1 + x2 + x3 + x4 = 1: distance = 1/||(1,1,1,1)|| = 1/2
        // For x_i = 0: distance = 0 (but we need to shift for origin to be interior)

        // Actually, this simplex doesn't have origin in interior. Let me reconsider.
        // The standard simplex conv{0, e1, e2, e3, e4} has origin on the boundary.
        // We need to shift it or use a different simplex.

        // Let's use the simplex centered at origin:
        // vertices at: (-1/4, -1/4, -1/4, -1/4) + e_i for i=1..4, plus (-1/4, -1/4, -1/4, -1/4)
        // Actually, simpler: use vertices (1,0,0,0), (0,1,0,0), (0,0,1,0), (0,0,0,1), (-1/4,-1/4,-1/4,-1/4)

        // Even simpler: regular 4-simplex with center at origin
        // vertices equally spaced on a sphere

        // Let me use a concrete example: the simplex with vertices:
        // v0 = (1, 0, 0, 0)
        // v1 = (0, 1, 0, 0)
        // v2 = (0, 0, 1, 0)
        // v3 = (0, 0, 0, 1)
        // v4 = (-1/4, -1/4, -1/4, -1/4)

        // Actually, the simplest is the regular 4-simplex inscribed in S³.
        // Let me compute its H-rep directly.

        // For now, let me use a simpler test case and come back to simplex later.

        // Use a simplex with vertices at distance 1 from origin in symmetric positions
        // 5 vertices in R⁴ that form a regular simplex centered at origin

        // Standard construction: 5 points equally distributed on S³
        // Project regular 4-simplex in R⁵ onto hyperplane x₀+x₁+x₂+x₃+x₄=0

        // Simplified: use the simplex with vertices:
        // e1, e2, e3, e4, -1/4(e1+e2+e3+e4)
        // Centroid is at origin, and we can compute H-rep.

        // I'll compute this properly in the test.

        // For now, let's use a simple cross-polytope instead for testing.
        unimplemented!("Use cross-polytope test instead")
    }

    /// Create a 4-dimensional cross-polytope (hyperoctahedron)
    /// Vertices at ±e_i for i=1..4
    /// Volume = 8/3 ≈ 2.6667
    fn make_cross_polytope() -> (Vec<Vector4<f64>>, Vec<f64>) {
        // 8 vertices at ±e_i
        // This has 2^4 = 16 facets (one for each orthant)

        let sqrt_4 = 2.0;
        let norm = 1.0 / sqrt_4;

        let mut normals = Vec::new();
        let mut heights = Vec::new();

        // All 16 combinations of signs for the normal (1,1,1,1)
        for s1 in &[-1.0, 1.0] {
            for s2 in &[-1.0, 1.0] {
                for s3 in &[-1.0, 1.0] {
                    for s4 in &[-1.0, 1.0] {
                        normals.push(Vector4::new(s1 * norm, s2 * norm, s3 * norm, s4 * norm));
                        heights.push(norm); // Distance from origin to facet
                    }
                }
            }
        }

        (normals, heights)
    }

    #[test]
    fn test_tesseract_volume() {
        let (normals, heights) = make_tesseract();
        let volume = polytope_volume_hrep(&normals, &heights).unwrap();

        // Tesseract [-1, 1]⁴ has volume (2)⁴ = 16
        assert!(
            (volume - 16.0).abs() < TOL,
            "tesseract volume: expected 16.0, got {volume}"
        );
    }

    #[test]
    fn test_cross_polytope_volume() {
        let (normals, heights) = make_cross_polytope();
        let volume = polytope_volume_hrep(&normals, &heights).unwrap();

        // Cross-polytope volume = 2^n / n! = 16 / 24 = 2/3 ≈ 0.6667
        let expected = 2.0 / 3.0;
        assert!(
            (volume - expected).abs() < TOL,
            "cross-polytope volume: expected {expected}, got {volume}"
        );
    }

    #[test]
    fn test_dimension_mismatch() {
        let normals = vec![Vector4::new(1.0, 0.0, 0.0, 0.0)];
        let heights = vec![1.0, 2.0];
        let result = polytope_volume_hrep(&normals, &heights);
        assert!(matches!(result, Err(VolumeError::DimensionMismatch { .. })));
    }

    #[test]
    fn test_empty_input() {
        let normals = vec![];
        let heights = vec![];
        let result = polytope_volume_hrep(&normals, &heights);
        assert!(matches!(result, Err(VolumeError::EmptyInput)));
    }
}
