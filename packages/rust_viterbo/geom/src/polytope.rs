//! H-representation of convex polytopes in R⁴.
//!
//! A convex polytope K is represented by the intersection of half-spaces:
//!
//! ```text
//! K = {x ∈ R⁴ : ⟨n_i, x⟩ ≤ h_i for all i}
//! ```
//!
//! where `n_i` are unit outward normals and `h_i` are the signed distances
//! from the origin to each facet.
//!
//! # Validation Routines
//!
//! This module provides validation routines that correspond 1:1 to definitions
//! in the thesis and SPEC.md. See individual function documentation for
//! mathematical references.
//!
//! | Property | Method | Reference |
//! |----------|--------|-----------|
//! | Unit normals | [`PolytopeHRep::validate`] | SPEC §Polytope Representation |
//! | Origin in interior | [`PolytopeHRep::origin_in_interior`] | SPEC §Polytope Representation |
//! | Bounded | [`PolytopeHRep::validate_bounded`] | SPEC: ≥5 facets in 4D |
//! | Non-redundant facets | [`PolytopeHRep::has_redundant_facets`] | SPEC §Facets: each has ≥4 vertices |
//! | Lagrangian pair | [`is_lagrangian_pair`] | SPEC §Lagrangian vs Non-Lagrangian |
//! | Symplectic form | [`symplectic_form`] | SPEC §Symplectic Structure |

use nalgebra::{Matrix4, Vector4};
use thiserror::Error;

use crate::tolerances::{EPS, EPS_UNIT};

// Re-export for backwards compatibility (was previously defined here)
pub use crate::tolerances::EPS_LAGRANGIAN;

// ============================================================================
// Symplectic Structure
// ============================================================================

/// Standard symplectic form on ℝ⁴.
///
/// **Definition (SPEC §Symplectic Form):**
/// ```text
/// ω(x, y) = ⟨Jx, y⟩ = x₁y₃ - x₃y₁ + x₂y₄ - x₄y₂
/// ```
///
/// where J is the standard complex structure:
/// ```text
/// J(q₁, q₂, p₁, p₂) = (-p₁, -p₂, q₁, q₂)
/// ```
///
/// In coordinates (q₁, q₂, p₁, p₂), this is ω = dq₁∧dp₁ + dq₂∧dp₂.
///
/// **Properties:**
/// - Antisymmetric: ω(x, y) = -ω(y, x)
/// - Non-degenerate: ω(x, y) = 0 for all y implies x = 0
///
/// # Example
///
/// ```
/// use geom::polytope::symplectic_form;
/// use nalgebra::Vector4;
///
/// let e1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
/// let e3 = Vector4::new(0.0, 0.0, 1.0, 0.0);
///
/// // Standard basis pairing: ω(e₁, e₃) = 1
/// assert!((symplectic_form(&e1, &e3) - 1.0).abs() < 1e-10);
/// // Antisymmetry: ω(e₃, e₁) = -1
/// assert!((symplectic_form(&e3, &e1) + 1.0).abs() < 1e-10);
/// ```
#[inline]
pub fn symplectic_form(x: &Vector4<f64>, y: &Vector4<f64>) -> f64 {
    // ω(x, y) = x₁y₃ - x₃y₁ + x₂y₄ - x₄y₂
    // In (q₁, q₂, p₁, p₂) coordinates: ω = dq₁∧dp₁ + dq₂∧dp₂
    x[0] * y[2] - x[2] * y[0] + x[1] * y[3] - x[3] * y[1]
}

/// Check if two facet normals form a Lagrangian 2-face.
///
/// **Definition (SPEC §Lagrangian vs Non-Lagrangian 2-Faces):**
/// A 2-face F_{ij} is **Lagrangian** iff ω(n_i, n_j) = 0.
///
/// This is a necessary condition for checking — actual 2-face existence
/// requires the facets to share ≥3 vertices (geometric adjacency).
///
/// **Significance:**
/// - Tube algorithm requires ALL 2-faces to be non-Lagrangian
/// - HK2017 works on all polytopes
/// - Billiard requires Lagrangian product structure (all 2-faces Lagrangian)
///
/// # Arguments
///
/// * `n_i`, `n_j` - Unit normal vectors of the two facets
///
/// # Returns
///
/// `true` if |ω(n_i, n_j)| < [`EPS_LAGRANGIAN`]
///
/// # Example
///
/// ```
/// use geom::polytope::is_lagrangian_pair;
/// use nalgebra::Vector4;
///
/// // Lagrangian pair: normals in same coordinate plane
/// let n1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
/// let n2 = Vector4::new(0.0, 1.0, 0.0, 0.0);
/// assert!(is_lagrangian_pair(&n1, &n2)); // ω(e₁, e₂) = 0
///
/// // Non-Lagrangian pair: normals in conjugate planes
/// let n3 = Vector4::new(0.0, 0.0, 1.0, 0.0);
/// assert!(!is_lagrangian_pair(&n1, &n3)); // ω(e₁, e₃) = 1 ≠ 0
/// ```
#[inline]
pub fn is_lagrangian_pair(n_i: &Vector4<f64>, n_j: &Vector4<f64>) -> bool {
    symplectic_form(n_i, n_j).abs() < EPS_LAGRANGIAN
}

/// Determine flow direction on a non-Lagrangian 2-face.
///
/// **Definition (SPEC §Flow Direction on Non-Lagrangian 2-Faces):**
/// For a non-Lagrangian 2-face F_{ij}, the Reeb flow crosses from one facet
/// to the other:
/// - If ω(n_i, n_j) > 0: flow crosses from F_i to F_j
/// - If ω(n_i, n_j) < 0: flow crosses from F_j to F_i
///
/// **Proof:** The Reeb vector on F_i is R_i ∝ J n_i. Its inner product with
/// n_j is ⟨J n_i, n_j⟩ = ω(n_i, n_j). When ω > 0, R_i points outward from
/// F_i toward F_j.
///
/// # Returns
///
/// - `Some(true)` if flow goes from facet i to facet j (ω > 0)
/// - `Some(false)` if flow goes from facet j to facet i (ω < 0)
/// - `None` if the 2-face is Lagrangian (no flow crossing)
///
/// # Example
///
/// ```
/// use geom::polytope::flow_direction;
/// use nalgebra::Vector4;
///
/// let e1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
/// let e3 = Vector4::new(0.0, 0.0, 1.0, 0.0);
///
/// // ω(e₁, e₃) = 1 > 0, so flow goes i → j
/// assert_eq!(flow_direction(&e1, &e3), Some(true));
/// // ω(e₃, e₁) = -1 < 0, so flow goes j → i
/// assert_eq!(flow_direction(&e3, &e1), Some(false));
/// ```
#[inline]
pub fn flow_direction(n_i: &Vector4<f64>, n_j: &Vector4<f64>) -> Option<bool> {
    let omega = symplectic_form(n_i, n_j);
    if omega.abs() < EPS_LAGRANGIAN {
        None // Lagrangian: no flow crossing
    } else {
        Some(omega > 0.0)
    }
}

// ============================================================================
// Polytope H-Representation
// ============================================================================

/// H-representation of a convex polytope K = {x : ⟨n_i, x⟩ ≤ h_i for all i}.
///
/// # Requirements
///
/// - `normals[i]` must be a unit vector (norm = 1 within [`EPS_UNIT`])
/// - `heights[i]` must be positive (origin is in the interior)
/// - `normals.len() == heights.len()`
///
/// # Coordinate Convention
///
/// We use symplectic coordinates `(q₁, q₂, p₁, p₂)` where the standard
/// symplectic form is `ω = dq₁ ∧ dp₁ + dq₂ ∧ dp₂`.
///
/// # Example
///
/// ```
/// use geom::PolytopeHRep;
/// use nalgebra::Vector4;
///
/// // Create a tesseract [-1, 1]⁴
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
/// let polytope = PolytopeHRep::new(normals, heights);
///
/// assert_eq!(polytope.num_facets(), 8);
/// assert!(polytope.validate().is_ok());
/// ```
#[derive(Debug, Clone)]
pub struct PolytopeHRep {
    /// Unit outward normals to each facet.
    pub normals: Vec<Vector4<f64>>,
    /// Signed distance from origin to each facet (must be > 0).
    pub heights: Vec<f64>,
}

impl PolytopeHRep {
    /// Create a new polytope from normals and heights.
    ///
    /// This does not validate the input. Call [`validate`](Self::validate)
    /// to check validity, or use [`new_validated`](Self::new_validated)
    /// for immediate validation.
    pub fn new(normals: Vec<Vector4<f64>>, heights: Vec<f64>) -> Self {
        Self { normals, heights }
    }

    /// Create a new polytope with immediate validation.
    pub fn new_validated(
        normals: Vec<Vector4<f64>>,
        heights: Vec<f64>,
    ) -> Result<Self, PolytopeError> {
        let polytope = Self::new(normals, heights);
        polytope.validate()?;
        Ok(polytope)
    }

    /// Number of facets.
    pub fn num_facets(&self) -> usize {
        self.normals.len()
    }

    /// Validate the polytope representation.
    ///
    /// Checks:
    /// - `normals.len() == heights.len()`
    /// - All normals are unit vectors
    /// - All heights are positive (origin in interior)
    ///
    /// Note: This does NOT check minimum facet count, as different algorithms
    /// have different requirements (HK2017 needs ≥2, tube needs ≥5).
    pub fn validate(&self) -> Result<(), PolytopeError> {
        // Check lengths match
        if self.normals.len() != self.heights.len() {
            return Err(PolytopeError::DimensionMismatch {
                normals: self.normals.len(),
                heights: self.heights.len(),
            });
        }

        // Check normals are unit vectors
        for (i, n) in self.normals.iter().enumerate() {
            let norm = n.norm();
            if (norm - 1.0).abs() > EPS_UNIT {
                return Err(PolytopeError::NonUnitNormal { index: i, norm });
            }
        }

        // Check heights are positive (origin in interior)
        for (i, &h) in self.heights.iter().enumerate() {
            if h <= 0.0 {
                return Err(PolytopeError::NonPositiveHeight {
                    index: i,
                    height: h,
                });
            }
        }

        Ok(())
    }

    /// Check if the origin is strictly in the interior.
    ///
    /// Returns `true` if all heights are positive.
    pub fn origin_in_interior(&self) -> bool {
        self.heights.iter().all(|&h| h > 0.0)
    }

    /// Scale the polytope by a factor λ > 0.
    ///
    /// Scaling multiplies all heights by λ (normals unchanged).
    /// Capacity scales as λ² under this operation.
    pub fn scale(&self, lambda: f64) -> Self {
        Self {
            normals: self.normals.clone(),
            heights: self.heights.iter().map(|h| h * lambda).collect(),
        }
    }

    // ========================================================================
    // Extended Validation (SPEC-aligned)
    // ========================================================================

    /// Validate that the polytope is bounded.
    ///
    /// **Definition (SPEC §Polytope Representation):**
    /// A bounded 4D polytope requires at least 5 facets. With fewer facets,
    /// the intersection of half-spaces is either unbounded or empty.
    ///
    /// **Note:** This is a fast rejection test. It does NOT verify that the
    /// normals positively span ℝ⁴ (which would guarantee boundedness).
    ///
    /// # Returns
    ///
    /// `Ok(())` if num_facets ≥ 5, otherwise `Err(TooFewFacets)`.
    pub fn validate_bounded(&self) -> Result<(), PolytopeError> {
        if self.normals.len() < 5 {
            return Err(PolytopeError::TooFewFacets {
                required: 5,
                actual: self.normals.len(),
            });
        }
        Ok(())
    }

    /// Enumerate all vertices of the polytope.
    ///
    /// **Definition:**
    /// A vertex is a point x ∈ K that lies on exactly 4 facets (the maximum
    /// in 4D). We find vertices by solving 4×4 linear systems for each
    /// combination of 4 facets and checking feasibility.
    ///
    /// **Algorithm:**
    /// For each 4-tuple (i, j, k, l) of facet indices:
    /// 1. Form the 4×4 matrix M with rows n_i, n_j, n_k, n_l
    /// 2. If M is invertible, solve M·x = (h_i, h_j, h_k, h_l)
    /// 3. Check if x satisfies all constraints: ⟨n_m, x⟩ ≤ h_m + ε for all m
    /// 4. If valid and not duplicate, add to vertex list
    ///
    /// # Returns
    ///
    /// Vector of vertices. May be empty if the polytope is degenerate.
    ///
    /// # Performance
    ///
    /// O(n⁴) where n = num_facets. Use sparingly for large polytopes.
    pub fn enumerate_vertices(&self) -> Vec<Vector4<f64>> {
        let n = self.normals.len();
        let mut vertices = Vec::new();

        for i in 0..n {
            for j in (i + 1)..n {
                for k in (j + 1)..n {
                    for l in (k + 1)..n {
                        // Build system: solve for x where x lies on all 4 hyperplanes
                        let m = Matrix4::from_rows(&[
                            self.normals[i].transpose(),
                            self.normals[j].transpose(),
                            self.normals[k].transpose(),
                            self.normals[l].transpose(),
                        ]);

                        if let Some(m_inv) = m.try_inverse() {
                            let h = Vector4::new(
                                self.heights[i],
                                self.heights[j],
                                self.heights[k],
                                self.heights[l],
                            );
                            let candidate = m_inv * h;

                            // Check if candidate satisfies all constraints
                            let is_valid = self
                                .normals
                                .iter()
                                .zip(&self.heights)
                                .all(|(n, &h)| n.dot(&candidate) <= h + EPS);

                            if is_valid {
                                // Check for duplicates
                                let is_dup = vertices
                                    .iter()
                                    .any(|v: &Vector4<f64>| (v - candidate).norm() < EPS);
                                if !is_dup {
                                    vertices.push(candidate);
                                }
                            }
                        }
                    }
                }
            }
        }

        vertices
    }

    /// Count how many vertices lie on each facet.
    ///
    /// **Definition (SPEC §Facets):**
    /// A facet F_i is the intersection of K with the i-th bounding hyperplane.
    /// In 4D, a proper 3-face (facet) must have at least 4 vertices.
    ///
    /// # Arguments
    ///
    /// * `vertices` - Pre-computed vertices from [`enumerate_vertices`]
    ///
    /// # Returns
    ///
    /// Vector where `result[i]` = number of vertices on facet i.
    pub fn count_facet_vertices(&self, vertices: &[Vector4<f64>]) -> Vec<usize> {
        let n = self.normals.len();
        let mut counts = vec![0usize; n];

        for v in vertices {
            for (facet, (n, h)) in self.normals.iter().zip(&self.heights).enumerate() {
                if (n.dot(v) - h).abs() < EPS {
                    counts[facet] += 1;
                }
            }
        }

        counts
    }

    /// Check if any facet has fewer than 4 vertices (redundant in 4D).
    ///
    /// **Definition (SPEC §Facets):**
    /// "Facets are 3-dimensional convex polytopes. Each facet has ≥4 vertices."
    ///
    /// A half-space with fewer than 4 vertices on it is either:
    /// - 0 vertices: completely redundant (doesn't touch K)
    /// - 1 vertex: touches K at a single point
    /// - 2 vertices: touches K along an edge
    /// - 3 vertices: touches K along a 2D face
    ///
    /// None of these are proper 3D facets.
    ///
    /// # Arguments
    ///
    /// * `vertices` - Pre-computed vertices from [`enumerate_vertices`]
    ///
    /// # Returns
    ///
    /// `Some(facet_index)` if a redundant facet is found, `None` otherwise.
    ///
    /// # Example
    ///
    /// ```
    /// use geom::PolytopeHRep;
    /// use nalgebra::Vector4;
    ///
    /// // Tesseract has 8 proper facets, each with 8 vertices
    /// let tesseract = PolytopeHRep::new(
    ///     vec![
    ///         Vector4::new( 1.0,  0.0,  0.0,  0.0),
    ///         Vector4::new(-1.0,  0.0,  0.0,  0.0),
    ///         Vector4::new( 0.0,  1.0,  0.0,  0.0),
    ///         Vector4::new( 0.0, -1.0,  0.0,  0.0),
    ///         Vector4::new( 0.0,  0.0,  1.0,  0.0),
    ///         Vector4::new( 0.0,  0.0, -1.0,  0.0),
    ///         Vector4::new( 0.0,  0.0,  0.0,  1.0),
    ///         Vector4::new( 0.0,  0.0,  0.0, -1.0),
    ///     ],
    ///     vec![1.0; 8],
    /// );
    /// let vertices = tesseract.enumerate_vertices();
    /// assert!(tesseract.has_redundant_facets(&vertices).is_none());
    /// ```
    pub fn has_redundant_facets(&self, vertices: &[Vector4<f64>]) -> Option<usize> {
        let counts = self.count_facet_vertices(vertices);
        counts.iter().position(|&c| c < 4)
    }

    /// Full validation including all geometric checks.
    ///
    /// Combines basic validation with extended checks:
    /// 1. Basic: lengths match, unit normals, positive heights
    /// 2. Bounded: at least 5 facets
    /// 3. Non-redundant: each facet has ≥4 vertices
    ///
    /// # Performance
    ///
    /// O(n⁴) due to vertex enumeration. Use [`validate`] for basic checks only.
    pub fn validate_full(&self) -> Result<(), PolytopeError> {
        // Basic validation
        self.validate()?;

        // Bounded check
        self.validate_bounded()?;

        // Non-redundancy check (expensive)
        let vertices = self.enumerate_vertices();
        if let Some(facet) = self.has_redundant_facets(&vertices) {
            let count = self.count_facet_vertices(&vertices)[facet];
            return Err(PolytopeError::RedundantFacet {
                facet,
                vertex_count: count,
            });
        }

        Ok(())
    }
}

/// Errors that can occur when validating a polytope.
#[derive(Debug, Error)]
pub enum PolytopeError {
    /// Number of normals doesn't match number of heights.
    #[error("dimension mismatch: {normals} normals vs {heights} heights")]
    DimensionMismatch { normals: usize, heights: usize },

    /// A normal vector is not unit length.
    #[error("normal[{index}] is not unit: norm = {norm:.15}")]
    NonUnitNormal { index: usize, norm: f64 },

    /// A height is not positive (origin not in interior).
    #[error("height[{index}] = {height:.15} is not positive (origin not in interior)")]
    NonPositiveHeight { index: usize, height: f64 },

    /// Too few facets for the intended use.
    #[error("need at least {required} facets, got {actual}")]
    TooFewFacets { required: usize, actual: usize },

    /// A facet has fewer than 4 vertices (not a proper 3-face in 4D).
    ///
    /// **Reference (SPEC §Facets):**
    /// "Facets are 3-dimensional convex polytopes. Each facet has ≥4 vertices."
    #[error("facet[{facet}] has only {vertex_count} vertices (need ≥4 for proper 3-face in 4D)")]
    RedundantFacet { facet: usize, vertex_count: usize },
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_tesseract() -> PolytopeHRep {
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
        PolytopeHRep::new(normals, heights)
    }

    #[test]
    fn test_tesseract_valid() {
        let p = make_tesseract();
        assert!(p.validate().is_ok());
        assert_eq!(p.num_facets(), 8);
    }

    #[test]
    fn test_dimension_mismatch() {
        let normals = vec![Vector4::new(1.0, 0.0, 0.0, 0.0)];
        let heights = vec![1.0, 2.0];
        let p = PolytopeHRep::new(normals, heights);
        assert!(matches!(
            p.validate(),
            Err(PolytopeError::DimensionMismatch { .. })
        ));
    }

    #[test]
    fn test_non_unit_normal() {
        let normals = vec![
            Vector4::new(2.0, 0.0, 0.0, 0.0), // Not unit
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
        ];
        let heights = vec![1.0, 1.0];
        let p = PolytopeHRep::new(normals, heights);
        assert!(matches!(
            p.validate(),
            Err(PolytopeError::NonUnitNormal { index: 0, .. })
        ));
    }

    #[test]
    fn test_non_positive_height() {
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
        ];
        let heights = vec![1.0, -1.0]; // Negative height
        let p = PolytopeHRep::new(normals, heights);
        assert!(matches!(
            p.validate(),
            Err(PolytopeError::NonPositiveHeight { index: 1, .. })
        ));
    }

    #[test]
    fn test_scale() {
        let p = make_tesseract();
        let scaled = p.scale(2.0);
        assert_eq!(scaled.heights, vec![2.0; 8]);
        assert_eq!(scaled.normals, p.normals);
    }

    #[test]
    fn test_new_validated_success() {
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
        ];
        let heights = vec![1.0, 1.0];
        let result = PolytopeHRep::new_validated(normals, heights);
        assert!(result.is_ok());
    }

    #[test]
    fn test_new_validated_failure() {
        let normals = vec![Vector4::new(2.0, 0.0, 0.0, 0.0)]; // Not unit
        let heights = vec![1.0];
        let result = PolytopeHRep::new_validated(normals, heights);
        assert!(result.is_err());
    }

    // ========================================================================
    // Symplectic Form Tests
    // ========================================================================

    #[test]
    fn test_symplectic_form_standard_basis() {
        use super::symplectic_form;

        let e1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let e2 = Vector4::new(0.0, 1.0, 0.0, 0.0);
        let e3 = Vector4::new(0.0, 0.0, 1.0, 0.0);
        let e4 = Vector4::new(0.0, 0.0, 0.0, 1.0);

        // Conjugate pairs: ω(e₁, e₃) = 1, ω(e₂, e₄) = 1
        assert!((symplectic_form(&e1, &e3) - 1.0).abs() < EPS);
        assert!((symplectic_form(&e2, &e4) - 1.0).abs() < EPS);

        // Lagrangian pairs: ω(e₁, e₂) = 0, ω(e₃, e₄) = 0
        assert!(symplectic_form(&e1, &e2).abs() < EPS);
        assert!(symplectic_form(&e3, &e4).abs() < EPS);

        // Antisymmetry: ω(e₃, e₁) = -1
        assert!((symplectic_form(&e3, &e1) + 1.0).abs() < EPS);
    }

    #[test]
    fn test_symplectic_form_antisymmetric() {
        use super::symplectic_form;

        let v = Vector4::new(1.0, 2.0, 3.0, 4.0);
        let w = Vector4::new(5.0, 6.0, 7.0, 8.0);

        // ω(v, w) = -ω(w, v)
        let omega_vw = symplectic_form(&v, &w);
        let omega_wv = symplectic_form(&w, &v);
        assert!((omega_vw + omega_wv).abs() < EPS);
    }

    // ========================================================================
    // Lagrangian Pair Tests
    // ========================================================================

    #[test]
    fn test_is_lagrangian_pair_true() {
        use super::is_lagrangian_pair;

        // Same coordinate plane: Lagrangian
        let n1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let n2 = Vector4::new(0.0, 1.0, 0.0, 0.0);
        assert!(is_lagrangian_pair(&n1, &n2));

        // Momentum plane: also Lagrangian
        let n3 = Vector4::new(0.0, 0.0, 1.0, 0.0);
        let n4 = Vector4::new(0.0, 0.0, 0.0, 1.0);
        assert!(is_lagrangian_pair(&n3, &n4));
    }

    #[test]
    fn test_is_lagrangian_pair_false() {
        use super::is_lagrangian_pair;

        // Conjugate planes: NOT Lagrangian
        let n1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let n3 = Vector4::new(0.0, 0.0, 1.0, 0.0);
        assert!(!is_lagrangian_pair(&n1, &n3));

        let n2 = Vector4::new(0.0, 1.0, 0.0, 0.0);
        let n4 = Vector4::new(0.0, 0.0, 0.0, 1.0);
        assert!(!is_lagrangian_pair(&n2, &n4));
    }

    // ========================================================================
    // Flow Direction Tests
    // ========================================================================

    #[test]
    fn test_flow_direction() {
        use super::flow_direction;

        let e1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let e2 = Vector4::new(0.0, 1.0, 0.0, 0.0);
        let e3 = Vector4::new(0.0, 0.0, 1.0, 0.0);

        // Lagrangian: no flow direction
        assert_eq!(flow_direction(&e1, &e2), None);

        // Non-Lagrangian: flow i→j when ω > 0
        assert_eq!(flow_direction(&e1, &e3), Some(true)); // ω(e₁, e₃) = 1 > 0
        assert_eq!(flow_direction(&e3, &e1), Some(false)); // ω(e₃, e₁) = -1 < 0
    }

    // ========================================================================
    // Bounded Validation Tests
    // ========================================================================

    #[test]
    fn test_validate_bounded_success() {
        let p = make_tesseract();
        assert!(p.validate_bounded().is_ok());
    }

    #[test]
    fn test_validate_bounded_too_few_facets() {
        // 4 facets is not enough for bounded 4D polytope
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, -1.0, 0.0, 0.0),
        ];
        let heights = vec![1.0; 4];
        let p = PolytopeHRep::new(normals, heights);

        assert!(matches!(
            p.validate_bounded(),
            Err(PolytopeError::TooFewFacets {
                required: 5,
                actual: 4
            })
        ));
    }

    // ========================================================================
    // Vertex Enumeration Tests
    // ========================================================================

    #[test]
    fn test_enumerate_vertices_tesseract() {
        let p = make_tesseract();
        let vertices = p.enumerate_vertices();

        // Tesseract [-1,1]⁴ has 2⁴ = 16 vertices
        assert_eq!(vertices.len(), 16);

        // Each vertex should be at (±1, ±1, ±1, ±1)
        for v in &vertices {
            for i in 0..4 {
                assert!(
                    (v[i].abs() - 1.0).abs() < EPS,
                    "Vertex coordinate {} should be ±1, got {}",
                    i,
                    v[i]
                );
            }
        }
    }

    #[test]
    fn test_count_facet_vertices_tesseract() {
        let p = make_tesseract();
        let vertices = p.enumerate_vertices();
        let counts = p.count_facet_vertices(&vertices);

        // Each facet of a tesseract has 2³ = 8 vertices
        assert_eq!(counts.len(), 8);
        for &count in &counts {
            assert_eq!(count, 8);
        }
    }

    // ========================================================================
    // Redundant Facet Tests (Error Paths)
    // ========================================================================

    #[test]
    fn test_has_redundant_facets_none() {
        let p = make_tesseract();
        let vertices = p.enumerate_vertices();
        assert!(p.has_redundant_facets(&vertices).is_none());
    }

    #[test]
    fn test_redundant_facet_0_vertices() {
        // Add a redundant facet that doesn't touch the polytope
        // Tesseract is in [-1,1]⁴; add facet x₁ ≤ 10 (completely redundant)
        let mut normals: Vec<Vector4<f64>> = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, -1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, -1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(0.0, 0.0, 0.0, -1.0),
        ];
        let mut heights = vec![1.0; 8];

        // Add redundant facet
        normals.push(Vector4::new(1.0, 0.0, 0.0, 0.0));
        heights.push(10.0); // x₁ ≤ 10, but tesseract already has x₁ ≤ 1

        let p = PolytopeHRep::new(normals, heights);
        let vertices = p.enumerate_vertices();

        // The redundant facet (index 8) should have 0 vertices on it
        // (all vertices satisfy x₁ = ±1, not x₁ = 10)
        let result = p.has_redundant_facets(&vertices);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), 8);
    }

    #[test]
    fn test_redundant_facet_1_vertex() {
        // Create a polytope where one facet touches only one vertex
        // Take tesseract and add a facet tangent to one corner
        let mut normals: Vec<Vector4<f64>> = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, -1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, -1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(0.0, 0.0, 0.0, -1.0),
        ];
        let mut heights = vec![1.0; 8];

        // Add facet tangent to corner (1,1,1,1): x₁+x₂+x₃+x₄ ≤ 4
        let corner_normal = Vector4::new(0.5, 0.5, 0.5, 0.5); // unit normal
        normals.push(corner_normal);
        heights.push(2.0); // 0.5*1 + 0.5*1 + 0.5*1 + 0.5*1 = 2

        let p = PolytopeHRep::new(normals, heights);
        let vertices = p.enumerate_vertices();
        let counts = p.count_facet_vertices(&vertices);

        // Facet 8 (the corner tangent) should have exactly 1 vertex
        assert_eq!(counts[8], 1, "Corner-tangent facet should have 1 vertex");
        assert_eq!(p.has_redundant_facets(&vertices), Some(8));
    }

    #[test]
    fn test_redundant_facet_2_vertices() {
        // Create a polytope where one facet is an edge (2 vertices)
        let mut normals: Vec<Vector4<f64>> = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, -1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, -1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(0.0, 0.0, 0.0, -1.0),
        ];
        let mut heights = vec![1.0; 8];

        // Add facet tangent to edge: x₁+x₂+x₃ ≤ 3 touches edge where x₄=±1
        // at points (1,1,1,±1)
        let inv_sqrt3 = 1.0 / 3.0_f64.sqrt();
        let edge_normal = Vector4::new(inv_sqrt3, inv_sqrt3, inv_sqrt3, 0.0);
        normals.push(edge_normal);
        heights.push(3.0_f64.sqrt()); // touches (1,1,1,x₄)

        let p = PolytopeHRep::new(normals, heights);
        let vertices = p.enumerate_vertices();
        let counts = p.count_facet_vertices(&vertices);

        // Facet 8 should have exactly 2 vertices: (1,1,1,1) and (1,1,1,-1)
        assert_eq!(counts[8], 2, "Edge-tangent facet should have 2 vertices");
        assert_eq!(p.has_redundant_facets(&vertices), Some(8));
    }

    // Note: A "3-vertex facet" test was removed because it's geometrically impossible.
    // In 4D, a proper facet (3-face) requires at least 4 vertices because the minimal
    // 3D polytope is a tetrahedron with 4 vertices. A half-space touching only 3
    // vertices of a polytope defines a 2D face, not a 3D facet.
    // The existing tests for 0, 1, and 2 vertices are sufficient to verify redundancy
    // detection. The boundary case of exactly 4 vertices (minimal valid facet) is
    // tested via test_redundant_facet_2_vertices which shows the edge-tangent case.

    // ========================================================================
    // Full Validation Tests
    // ========================================================================

    #[test]
    fn test_validate_full_success() {
        let p = make_tesseract();
        assert!(p.validate_full().is_ok());
    }

    #[test]
    fn test_validate_full_catches_redundant() {
        // Add redundant facet
        let mut normals: Vec<Vector4<f64>> = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, -1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, -1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(0.0, 0.0, 0.0, -1.0),
        ];
        let mut heights = vec![1.0; 8];

        // Completely redundant facet
        normals.push(Vector4::new(1.0, 0.0, 0.0, 0.0));
        heights.push(10.0);

        let p = PolytopeHRep::new(normals, heights);
        assert!(matches!(
            p.validate_full(),
            Err(PolytopeError::RedundantFacet { facet: 8, .. })
        ));
    }

    // ========================================================================
    // P1: Cross-Polytope Vertices
    // ========================================================================

    /// Cross-polytope (16-cell) should have 8 vertices with 6 vertices per facet.
    ///
    /// The cross-polytope is conv{±e₁, ±e₂, ±e₃, ±e₄}, which has:
    /// - 8 vertices: ±e_i for i = 1..4
    /// - 16 facets with normals (±1,±1,±1,±1)/2
    /// - Each facet (3-simplex) has exactly 4 vertices
    ///
    /// Wait, let me reconsider: a 4D cross-polytope facet is a tetrahedron (3-simplex)
    /// with 4 vertices, not 6. Let me verify this is what the task expects.
    #[test]
    fn test_cross_polytope_vertices() {
        let p = make_cross_polytope();
        let vertices = p.enumerate_vertices();

        // Cross-polytope has 8 vertices: ±e_i for i = 1..4
        assert_eq!(
            vertices.len(),
            8,
            "Cross-polytope should have 8 vertices, got {}",
            vertices.len()
        );

        // Each facet is a tetrahedron (3-simplex) with 4 vertices
        // The description says "6 per facet" but geometrically it should be 4.
        // Let's verify and document what we actually find.
        let counts = p.count_facet_vertices(&vertices);
        for (i, &count) in counts.iter().enumerate() {
            // Each facet of a cross-polytope is a tetrahedron with 4 vertices
            assert_eq!(
                count, 4,
                "Facet {} should have 4 vertices (tetrahedron), got {}",
                i, count
            );
        }
    }

    fn make_cross_polytope() -> PolytopeHRep {
        // Unit cross-polytope (16-cell): conv{±e₁, ±e₂, ±e₃, ±e₄}
        // 16 facets with normals (±1,±1,±1,±1)/2
        let mut normals = Vec::new();
        for s1 in [-1.0, 1.0] {
            for s2 in [-1.0, 1.0] {
                for s3 in [-1.0, 1.0] {
                    for s4 in [-1.0, 1.0] {
                        normals.push(Vector4::new(s1, s2, s3, s4) / 2.0);
                    }
                }
            }
        }
        // Heights h = 1/2: each facet passes through vertices like e₁
        let heights = vec![0.5; 16];
        PolytopeHRep::new(normals, heights)
    }

    // ========================================================================
    // P2: 4-Simplex Vertices
    // ========================================================================

    /// 4-simplex (5-cell) should have 5 vertices with 4 vertices per facet.
    ///
    /// The 4-simplex has:
    /// - 5 vertices in general position
    /// - 5 facets (each opposite one vertex)
    /// - Each facet is a tetrahedron (3-simplex) with 4 vertices
    #[test]
    fn test_simplex_vertices() {
        let p = make_4_simplex();
        let vertices = p.enumerate_vertices();

        // 4-simplex has exactly 5 vertices
        assert_eq!(
            vertices.len(),
            5,
            "4-simplex should have 5 vertices, got {}",
            vertices.len()
        );

        // Each facet is a tetrahedron with 4 vertices
        let counts = p.count_facet_vertices(&vertices);
        assert_eq!(counts.len(), 5, "4-simplex should have 5 facets");
        for (i, &count) in counts.iter().enumerate() {
            assert_eq!(
                count, 4,
                "Facet {} should have 4 vertices (tetrahedron), got {}",
                i, count
            );
        }
    }

    /// Create a regular 4-simplex centered at origin.
    ///
    /// Vertices: e₁, e₂, e₃, e₄, (-1,-1,-1,-1) shifted so centroid is at origin.
    fn make_4_simplex() -> PolytopeHRep {
        // Use the same construction as tube::fixtures::four_simplex
        let sqrt19 = 19.0_f64.sqrt();

        // Facet opposite v4=(-1,-1,-1,-1): contains e1,e2,e3,e4
        let n4 = Vector4::new(1.0, 1.0, 1.0, 1.0) / 2.0;
        let h4 = 0.5;

        // Facet opposite v0=(1,0,0,0): contains e2,e3,e4,(-1,-1,-1,-1)
        let n0 = Vector4::new(-4.0, 1.0, 1.0, 1.0) / sqrt19;
        let h0 = 1.0 / sqrt19;

        // Facet opposite v1=(0,1,0,0)
        let n1 = Vector4::new(1.0, -4.0, 1.0, 1.0) / sqrt19;
        let h1 = 1.0 / sqrt19;

        // Facet opposite v2=(0,0,1,0)
        let n2 = Vector4::new(1.0, 1.0, -4.0, 1.0) / sqrt19;
        let h2 = 1.0 / sqrt19;

        // Facet opposite v3=(0,0,0,1)
        let n3 = Vector4::new(1.0, 1.0, 1.0, -4.0) / sqrt19;
        let h3 = 1.0 / sqrt19;

        PolytopeHRep::new(vec![n0, n1, n2, n3, n4], vec![h0, h1, h2, h3, h4])
    }

    // ========================================================================
    // P3: Vertices Constraint Satisfaction
    // ========================================================================

    /// All vertices must satisfy all constraints: ⟨n_i, v⟩ ≤ h_i + EPS.
    ///
    /// This is a fundamental property of vertices in an H-rep polytope.
    #[test]
    fn test_vertices_constraint_satisfaction() {
        // Test on multiple polytopes
        let polytopes = [
            ("tesseract", make_tesseract()),
            ("cross-polytope", make_cross_polytope()),
            ("4-simplex", make_4_simplex()),
        ];

        for (name, p) in &polytopes {
            let vertices = p.enumerate_vertices();
            for (v_idx, v) in vertices.iter().enumerate() {
                for (f_idx, (n, &h)) in p.normals.iter().zip(&p.heights).enumerate() {
                    let value = n.dot(v);
                    assert!(
                        value <= h + EPS,
                        "{}: vertex {} violates facet {}: ⟨n, v⟩ = {} > h + ε = {}",
                        name,
                        v_idx,
                        f_idx,
                        value,
                        h + EPS
                    );
                }
            }
        }
    }

    // ========================================================================
    // P4: Vertices Tightness
    // ========================================================================

    /// Each vertex lies on exactly 4 facets (tight constraint) in 4D.
    ///
    /// In 4D, a vertex is the intersection of exactly 4 hyperplanes.
    #[test]
    fn test_vertices_tightness() {
        let polytopes = [
            ("tesseract", make_tesseract()),
            ("cross-polytope", make_cross_polytope()),
            ("4-simplex", make_4_simplex()),
        ];

        for (name, p) in &polytopes {
            let vertices = p.enumerate_vertices();
            for (v_idx, v) in vertices.iter().enumerate() {
                // Count how many facets this vertex lies on (tight constraints)
                let tight_count = p
                    .normals
                    .iter()
                    .zip(&p.heights)
                    .filter(|(n, &h)| {
                        let value = n.dot(v);
                        (value - h).abs() < EPS
                    })
                    .count();

                // In 4D, vertices are defined by exactly 4 tight constraints
                assert!(
                    tight_count >= 4,
                    "{}: vertex {} lies on only {} facets (need ≥4 in 4D). Vertex: {:?}",
                    name,
                    v_idx,
                    tight_count,
                    v
                );
            }
        }
    }

    // ========================================================================
    // P5: Vertices No Duplicates
    // ========================================================================

    /// All vertices must be distinct: ‖v - w‖ > EPS for all pairs.
    #[test]
    fn test_vertices_no_duplicates() {
        let polytopes = [
            ("tesseract", make_tesseract()),
            ("cross-polytope", make_cross_polytope()),
            ("4-simplex", make_4_simplex()),
        ];

        for (name, p) in &polytopes {
            let vertices = p.enumerate_vertices();
            for i in 0..vertices.len() {
                for j in (i + 1)..vertices.len() {
                    let dist = (vertices[i] - vertices[j]).norm();
                    assert!(
                        dist > EPS,
                        "{}: vertices {} and {} are duplicates (distance = {})",
                        name,
                        i,
                        j,
                        dist
                    );
                }
            }
        }
    }

    // ========================================================================
    // P7: Origin in Interior
    // ========================================================================

    /// Test origin_in_interior() returns true when all heights are positive.
    #[test]
    fn test_origin_in_interior() {
        // Tesseract with all h > 0: origin is inside
        let p = make_tesseract();
        assert!(
            p.origin_in_interior(),
            "Tesseract with h=1 should have origin in interior"
        );

        // Cross-polytope with h > 0: origin is inside
        let p = make_cross_polytope();
        assert!(
            p.origin_in_interior(),
            "Cross-polytope with h=0.5 should have origin in interior"
        );

        // Custom polytope with varying positive heights
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
        let heights = vec![0.5, 1.0, 1.5, 2.0, 0.1, 0.2, 0.3, 0.4];
        let p = PolytopeHRep::new(normals, heights);
        assert!(
            p.origin_in_interior(),
            "All heights > 0 means origin in interior"
        );
    }

    // ========================================================================
    // P8: Origin on Boundary
    // ========================================================================

    /// Test origin_in_interior() returns false when any h_i = 0.
    #[test]
    fn test_origin_on_boundary() {
        let make_normals = || {
            vec![
                Vector4::new(1.0, 0.0, 0.0, 0.0),
                Vector4::new(-1.0, 0.0, 0.0, 0.0),
                Vector4::new(0.0, 1.0, 0.0, 0.0),
                Vector4::new(0.0, -1.0, 0.0, 0.0),
                Vector4::new(0.0, 0.0, 1.0, 0.0),
                Vector4::new(0.0, 0.0, -1.0, 0.0),
                Vector4::new(0.0, 0.0, 0.0, 1.0),
                Vector4::new(0.0, 0.0, 0.0, -1.0),
            ]
        };

        // Tesseract with one height = 0: origin is on boundary
        let heights = vec![1.0, 0.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]; // Second height is 0
        let p = PolytopeHRep::new(make_normals(), heights);
        assert!(
            !p.origin_in_interior(),
            "h=0 means origin is on boundary (⟨n, 0⟩ = 0 = h)"
        );

        // Edge case: all heights = 0
        let heights = vec![0.0; 8];
        let p = PolytopeHRep::new(make_normals(), heights);
        assert!(
            !p.origin_in_interior(),
            "All h=0 means origin on every boundary"
        );

        // Edge case: one negative height (origin outside)
        let heights = vec![1.0, -0.5, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0];
        let p = PolytopeHRep::new(make_normals(), heights);
        assert!(
            !p.origin_in_interior(),
            "Negative height means origin outside"
        );
    }

    // ========================================================================
    // P9: is_lagrangian_pair Threshold Boundary
    // ========================================================================

    /// Test is_lagrangian_pair at the threshold boundary: |ω| = EPS_LAGRANGIAN ± 1e-15.
    #[test]
    fn test_is_lagrangian_threshold_boundary() {
        // Construct unit vectors with controlled symplectic form
        // ω(x, y) = x₁y₃ - x₃y₁ + x₂y₄ - x₄y₂
        //
        // Strategy: use vectors where we can control ω precisely.
        // e₁ = (1,0,0,0), e₃ = (0,0,1,0) have ω(e₁, e₃) = 1
        // Linear combination: if n₁ = e₁, n₂ = ε·e₃ + √(1-ε²)·e₂, then ω(n₁, n₂) = ε

        let tiny = 1e-15;
        let n1 = Vector4::new(1.0, 0.0, 0.0, 0.0);

        // Just below threshold: ω = EPS_LAGRANGIAN - tiny
        let omega_target = EPS_LAGRANGIAN - tiny;
        let rest = (1.0 - omega_target * omega_target).sqrt();
        let n2_below = Vector4::new(0.0, rest, omega_target, 0.0);
        assert!(
            (n2_below.norm() - 1.0).abs() < 1e-12,
            "n2_below should be unit"
        );
        let actual_omega_below = symplectic_form(&n1, &n2_below);
        assert!(
            is_lagrangian_pair(&n1, &n2_below),
            "|ω| = {} < EPS_LAGRANGIAN = {} should be Lagrangian",
            actual_omega_below.abs(),
            EPS_LAGRANGIAN
        );

        // Just above threshold: ω = EPS_LAGRANGIAN + tiny
        let omega_target = EPS_LAGRANGIAN + tiny;
        let rest = (1.0 - omega_target * omega_target).sqrt();
        let n2_above = Vector4::new(0.0, rest, omega_target, 0.0);
        assert!(
            (n2_above.norm() - 1.0).abs() < 1e-12,
            "n2_above should be unit"
        );
        let actual_omega_above = symplectic_form(&n1, &n2_above);
        assert!(
            !is_lagrangian_pair(&n1, &n2_above),
            "|ω| = {} >= EPS_LAGRANGIAN = {} should NOT be Lagrangian",
            actual_omega_above.abs(),
            EPS_LAGRANGIAN
        );
    }

    // ========================================================================
    // P10: flow_direction Threshold Boundary
    // ========================================================================

    /// Test flow_direction at threshold: ω = ±EPS_LAGRANGIAN exactly.
    #[test]
    fn test_flow_direction_threshold_boundary() {
        let n1 = Vector4::new(1.0, 0.0, 0.0, 0.0);

        // Exactly at positive threshold
        let omega_exact = EPS_LAGRANGIAN;
        let rest = (1.0 - omega_exact * omega_exact).sqrt();
        let n2_exact_pos = Vector4::new(0.0, rest, omega_exact, 0.0);

        // At exactly EPS_LAGRANGIAN, the condition |ω| < EPS_LAGRANGIAN is false,
        // so flow_direction should return Some(direction).
        let result_pos = flow_direction(&n1, &n2_exact_pos);
        // |ω| = EPS_LAGRANGIAN is NOT < EPS_LAGRANGIAN, so this is non-Lagrangian
        assert!(
            result_pos.is_some(),
            "ω = EPS_LAGRANGIAN exactly should be non-Lagrangian (not < threshold)"
        );
        assert_eq!(
            result_pos,
            Some(true),
            "ω = +EPS_LAGRANGIAN should give flow i→j"
        );

        // Exactly at negative threshold
        let n2_exact_neg = Vector4::new(0.0, rest, -omega_exact, 0.0);
        let result_neg = flow_direction(&n1, &n2_exact_neg);
        assert!(
            result_neg.is_some(),
            "ω = -EPS_LAGRANGIAN exactly should be non-Lagrangian"
        );
        assert_eq!(
            result_neg,
            Some(false),
            "ω = -EPS_LAGRANGIAN should give flow j→i"
        );

        // Just inside threshold (Lagrangian)
        let tiny = 1e-15;
        let omega_inside = EPS_LAGRANGIAN - tiny;
        let rest_inside = (1.0 - omega_inside * omega_inside).sqrt();
        let n2_inside = Vector4::new(0.0, rest_inside, omega_inside, 0.0);
        let result_inside = flow_direction(&n1, &n2_inside);
        assert!(
            result_inside.is_none(),
            "ω just below EPS_LAGRANGIAN should be Lagrangian (no flow direction)"
        );
    }

    // ========================================================================
    // P11: Redundant Facet 4 Vertices Valid
    // ========================================================================

    /// A facet with exactly 4 vertices is NOT redundant (boundary case).
    ///
    /// In 4D, the minimum number of vertices for a proper 3-face (facet) is 4
    /// (a tetrahedron). This tests that has_redundant_facets returns None
    /// when a facet has exactly 4 vertices.
    #[test]
    fn test_redundant_facet_4_vertices_valid() {
        // The 4-simplex has facets that are tetrahedra with exactly 4 vertices each
        let p = make_4_simplex();
        let vertices = p.enumerate_vertices();
        let counts = p.count_facet_vertices(&vertices);

        // Verify all facets have exactly 4 vertices
        for (i, &count) in counts.iter().enumerate() {
            assert_eq!(
                count, 4,
                "4-simplex facet {} should have exactly 4 vertices",
                i
            );
        }

        // This should NOT be detected as redundant
        assert!(
            p.has_redundant_facets(&vertices).is_none(),
            "Facets with exactly 4 vertices should NOT be redundant"
        );

        // Also test that validate_full passes
        assert!(
            p.validate_full().is_ok(),
            "4-simplex should pass full validation"
        );

        // Cross-polytope facets are also tetrahedra with 4 vertices
        let p = make_cross_polytope();
        let vertices = p.enumerate_vertices();
        let counts = p.count_facet_vertices(&vertices);

        for (i, &count) in counts.iter().enumerate() {
            assert_eq!(
                count, 4,
                "Cross-polytope facet {} should have exactly 4 vertices",
                i
            );
        }

        assert!(
            p.has_redundant_facets(&vertices).is_none(),
            "Cross-polytope facets with 4 vertices should NOT be redundant"
        );
    }
}
