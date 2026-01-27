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

use nalgebra::Vector4;
use thiserror::Error;

use crate::tolerances::EPS_UNIT;

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
}
