//! H-representation of a 4D convex polytope.
//!
//! # Definition
//!
//! A polytope in **H-representation** (half-space representation) is defined as:
//!
//! ```text
//! K = ⋂ᵢ { x ∈ ℝ⁴ : ⟨nᵢ, x⟩ ≤ hᵢ }
//! ```
//!
//! where:
//! - `nᵢ` is the **outward unit normal** of the i-th facet
//! - `hᵢ > 0` is the **height** (signed distance from origin to hyperplane)
//!
//! # Mathematical Properties (Invariants)
//!
//! A valid [`HRep`] satisfies:
//!
//! 1. **At least 5 facets** (minimum for a 4D polytope with interior)
//! 2. **Unit normals**: ‖nᵢ‖ = 1 for all i
//! 3. **Positive heights**: hᵢ > 0 for all i (ensures 0 ∈ int(K))
//! 4. **Bounded**: The normals positively span ℝ⁴ (no recession direction)
//!
//! # Note on Irredundancy
//!
//! We do NOT currently check irredundancy (that each facet is essential).
//! Redundant facets don't affect correctness, only efficiency.
//!
//! # References
//!
//! - Definition of polytope: A bounded intersection of half-spaces.
//! - Origin in interior: Equivalent to all heights being positive when normals
//!   point outward.

use nalgebra::Vector4;
use thiserror::Error;

use crate::bounded::is_bounded;
use crate::tolerances::{EPS_HEIGHT, EPS_UNIT, MAX_COORD};

/// Error type for H-representation validation failures.
///
/// Each variant corresponds to a specific invariant violation.
#[derive(Debug, Clone, Error, PartialEq)]
pub enum HRepError {
    /// Polytope has fewer than 5 facets.
    #[error("H-rep must have at least 5 facets for a 4D polytope, got {0}")]
    TooFewFacets(usize),

    /// Normal vector count doesn't match height count.
    #[error("mismatched lengths: {num_normals} normals vs {num_heights} heights")]
    MismatchedLengths {
        num_normals: usize,
        num_heights: usize,
    },

    /// A normal or height coordinate is invalid (NaN, infinite, or too large).
    #[error(
        "{field} {index} has invalid value: {value} (must be finite and |x| <= {MAX_COORD:.0e})"
    )]
    InvalidCoordinate {
        field: &'static str,
        index: usize,
        value: f64,
    },

    /// A normal vector is not unit length.
    #[error("normal {index} has length {norm:.6}, expected 1.0 (tolerance {EPS_UNIT:.2e})")]
    NonUnitNormal { index: usize, norm: f64 },

    /// A height is not positive (origin not in interior).
    #[error("height {index} is {height:.6}, expected > 0 (origin must be in interior)")]
    NonPositiveHeight { index: usize, height: f64 },

    /// The polytope is unbounded (normals don't positively span ℝ⁴).
    #[error("polytope is unbounded: normals do not positively span R^4")]
    Unbounded,
}

/// H-representation of a 4D convex polytope.
///
/// # Invariants
///
/// All instances satisfy (enforced by [`HRep::new`]):
/// - At least 5 facets
/// - All normals are unit vectors
/// - All heights are positive (0 ∈ int(K))
/// - Polytope is bounded
///
/// # Example
///
/// ```
/// use nalgebra::Vector4;
/// use geom4d::HRep;
///
/// // Unit tesseract [-1, 1]⁴ (8 facets)
/// let normals = vec![
///     Vector4::new(1.0, 0.0, 0.0, 0.0),
///     Vector4::new(-1.0, 0.0, 0.0, 0.0),
///     Vector4::new(0.0, 1.0, 0.0, 0.0),
///     Vector4::new(0.0, -1.0, 0.0, 0.0),
///     Vector4::new(0.0, 0.0, 1.0, 0.0),
///     Vector4::new(0.0, 0.0, -1.0, 0.0),
///     Vector4::new(0.0, 0.0, 0.0, 1.0),
///     Vector4::new(0.0, 0.0, 0.0, -1.0),
/// ];
/// let heights = vec![1.0; 8];
///
/// let tesseract = HRep::new(normals, heights).expect("valid H-rep");
/// assert_eq!(tesseract.num_facets(), 8);
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct HRep {
    /// Outward unit normals of facets.
    normals: Vec<Vector4<f64>>,
    /// Heights (signed distances from origin to facet hyperplanes).
    heights: Vec<f64>,
}

impl HRep {
    /// Create a new H-representation, validating all invariants.
    ///
    /// # Errors
    ///
    /// Returns [`HRepError`] if any invariant is violated:
    /// - [`HRepError::MismatchedLengths`] if `normals.len() != heights.len()`
    /// - [`HRepError::TooFewFacets`] if fewer than 5 facets
    /// - [`HRepError::InvalidCoordinate`] if any coordinate is NaN, infinite, or `|x| > MAX_COORD`
    /// - [`HRepError::NonUnitNormal`] if any normal has ‖n‖ ≠ 1
    /// - [`HRepError::NonPositiveHeight`] if any height is ≤ 0
    /// - [`HRepError::Unbounded`] if normals don't positively span ℝ⁴
    ///
    /// # Validation Order
    ///
    /// Checks are performed in order of increasing computational cost:
    /// 1. Length matching and facet count (O(1))
    /// 2. Coordinate validity (O(n))
    /// 3. Unit normals (O(n))
    /// 4. Positive heights (O(n))
    /// 5. Boundedness via LP
    pub fn new(normals: Vec<Vector4<f64>>, heights: Vec<f64>) -> Result<Self, HRepError> {
        // Check 1: normals.len() == heights.len()
        if normals.len() != heights.len() {
            return Err(HRepError::MismatchedLengths {
                num_normals: normals.len(),
                num_heights: heights.len(),
            });
        }

        // Check 2: At least 5 facets
        if normals.len() < 5 {
            return Err(HRepError::TooFewFacets(normals.len()));
        }

        // Check 3: All coordinates must be finite and within MAX_COORD
        for (i, n) in normals.iter().enumerate() {
            for &coord in &[n.x, n.y, n.z, n.w] {
                if !coord.is_finite() || coord.abs() > MAX_COORD {
                    return Err(HRepError::InvalidCoordinate {
                        field: "normal",
                        index: i,
                        value: coord,
                    });
                }
            }
        }
        for (i, &h) in heights.iter().enumerate() {
            if !h.is_finite() || h.abs() > MAX_COORD {
                return Err(HRepError::InvalidCoordinate {
                    field: "height",
                    index: i,
                    value: h,
                });
            }
        }

        // Check 4: All normals are unit vectors
        for (i, n) in normals.iter().enumerate() {
            let norm = n.norm();
            if (norm - 1.0).abs() > EPS_UNIT {
                return Err(HRepError::NonUnitNormal { index: i, norm });
            }
        }

        // Check 5: All heights are positive
        for (i, &h) in heights.iter().enumerate() {
            if h <= EPS_HEIGHT {
                return Err(HRepError::NonPositiveHeight {
                    index: i,
                    height: h,
                });
            }
        }

        // Check 6: Polytope is bounded
        if !is_bounded(&normals) {
            return Err(HRepError::Unbounded);
        }

        Ok(Self { normals, heights })
    }

    /// Create an H-representation without validation.
    ///
    /// # Safety
    ///
    /// This is not unsafe in the Rust sense, but violating invariants will cause
    /// incorrect results from downstream algorithms.
    ///
    /// Use only when:
    /// - Data is known-good (e.g., from a trusted source)
    /// - Performance is critical and you've validated externally
    #[must_use]
    pub fn new_unchecked(normals: Vec<Vector4<f64>>, heights: Vec<f64>) -> Self {
        debug_assert_eq!(
            normals.len(),
            heights.len(),
            "normals and heights must have same length"
        );
        debug_assert!(normals.len() >= 5, "need at least 5 facets");
        Self { normals, heights }
    }

    /// Returns the outward unit normals.
    #[must_use]
    pub fn normals(&self) -> &[Vector4<f64>] {
        &self.normals
    }

    /// Returns the heights.
    #[must_use]
    pub fn heights(&self) -> &[f64] {
        &self.heights
    }

    /// Returns the number of facets.
    #[must_use]
    pub fn num_facets(&self) -> usize {
        self.normals.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    /// Helper: unit tesseract [-1, 1]⁴
    fn tesseract_hrep() -> (Vec<Vector4<f64>>, Vec<f64>) {
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

    /// Helper: unit cross-polytope (16 facets)
    fn cross_polytope_hrep() -> (Vec<Vector4<f64>>, Vec<f64>) {
        let mut normals = Vec::with_capacity(16);
        for s1 in [-1.0, 1.0] {
            for s2 in [-1.0, 1.0] {
                for s3 in [-1.0, 1.0] {
                    for s4 in [-1.0, 1.0] {
                        normals.push(Vector4::new(s1, s2, s3, s4).normalize());
                    }
                }
            }
        }
        // Cross-polytope with vertices at ±eᵢ has height 1/√4 = 0.5 for these normals
        let heights = vec![1.0; 16];
        (normals, heights)
    }

    /// Helper: minimal valid polytope (5-simplex-like, 5 facets)
    fn minimal_hrep() -> (Vec<Vector4<f64>>, Vec<f64>) {
        // Use simplex-like configuration: 5 normals that positively span R⁴
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(-1.0, -1.0, -1.0, -1.0).normalize(),
        ];
        let heights = vec![1.0; 5];
        (normals, heights)
    }

    // ==================== POSITIVE TESTS ====================

    #[test]
    fn test_new_accepts_tesseract() {
        let (normals, heights) = tesseract_hrep();
        let hrep = HRep::new(normals, heights);
        assert!(hrep.is_ok());
        assert_eq!(hrep.unwrap().num_facets(), 8);
    }

    #[test]
    fn test_new_accepts_cross_polytope() {
        let (normals, heights) = cross_polytope_hrep();
        let hrep = HRep::new(normals, heights);
        assert!(hrep.is_ok());
        assert_eq!(hrep.unwrap().num_facets(), 16);
    }

    #[test]
    fn test_new_accepts_minimal_polytope() {
        let (normals, heights) = minimal_hrep();
        let hrep = HRep::new(normals, heights);
        assert!(hrep.is_ok());
        assert_eq!(hrep.unwrap().num_facets(), 5);
    }

    #[test]
    fn test_accessors_return_correct_data() {
        let (normals, heights) = tesseract_hrep();
        let hrep = HRep::new(normals.clone(), heights.clone()).unwrap();

        assert_eq!(hrep.normals().len(), 8);
        assert_eq!(hrep.heights().len(), 8);

        for (i, n) in hrep.normals().iter().enumerate() {
            assert_relative_eq!(n.norm(), 1.0, epsilon = EPS_UNIT);
            assert_eq!(*n, normals[i]);
        }

        for (i, &h) in hrep.heights().iter().enumerate() {
            assert_eq!(h, heights[i]);
        }
    }

    // ==================== NEGATIVE TESTS ====================

    #[test]
    fn test_new_rejects_mismatched_lengths() {
        let normals = vec![Vector4::new(1.0, 0.0, 0.0, 0.0); 8];
        let heights = vec![1.0; 7]; // Mismatch!

        let result = HRep::new(normals, heights);
        assert!(matches!(
            result,
            Err(HRepError::MismatchedLengths {
                num_normals: 8,
                num_heights: 7
            })
        ));
    }

    #[test]
    fn test_new_rejects_too_few_facets_zero() {
        let result = HRep::new(vec![], vec![]);
        assert!(matches!(result, Err(HRepError::TooFewFacets(0))));
    }

    #[test]
    fn test_new_rejects_too_few_facets_four() {
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, -1.0, 0.0, 0.0),
        ];
        let heights = vec![1.0; 4];

        let result = HRep::new(normals, heights);
        assert!(matches!(result, Err(HRepError::TooFewFacets(4))));
    }

    #[test]
    fn test_new_rejects_non_unit_normal_too_long() {
        let (mut normals, heights) = tesseract_hrep();
        normals[3] = Vector4::new(0.0, -1.5, 0.0, 0.0); // Length 1.5, not unit

        let result = HRep::new(normals, heights);
        assert!(matches!(
            result,
            Err(HRepError::NonUnitNormal { index: 3, .. })
        ));
    }

    #[test]
    fn test_new_rejects_non_unit_normal_too_short() {
        let (mut normals, heights) = tesseract_hrep();
        normals[0] = Vector4::new(0.5, 0.0, 0.0, 0.0); // Length 0.5, not unit

        let result = HRep::new(normals, heights);
        assert!(matches!(
            result,
            Err(HRepError::NonUnitNormal { index: 0, .. })
        ));
    }

    #[test]
    fn test_new_rejects_zero_height() {
        let (normals, mut heights) = tesseract_hrep();
        heights[2] = 0.0;

        let result = HRep::new(normals, heights);
        assert!(matches!(
            result,
            Err(HRepError::NonPositiveHeight { index: 2, .. })
        ));
    }

    #[test]
    fn test_new_rejects_negative_height() {
        let (normals, mut heights) = tesseract_hrep();
        heights[5] = -1.0;

        let result = HRep::new(normals, heights);
        assert!(matches!(
            result,
            Err(HRepError::NonPositiveHeight { index: 5, .. })
        ));
    }

    #[test]
    fn test_new_rejects_unbounded_positive_orthant() {
        // All normals pointing in positive directions → unbounded in negative directions
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(1.0, 1.0, 0.0, 0.0).normalize(),
        ];
        let heights = vec![1.0; 5];

        let result = HRep::new(normals, heights);
        assert!(matches!(result, Err(HRepError::Unbounded)));
    }

    #[test]
    fn test_new_rejects_nan_in_normal() {
        let (mut normals, heights) = tesseract_hrep();
        normals[2] = Vector4::new(0.0, f64::NAN, 0.0, 0.0);

        let result = HRep::new(normals, heights);
        assert!(matches!(
            result,
            Err(HRepError::InvalidCoordinate {
                field: "normal",
                index: 2,
                ..
            })
        ));
    }

    #[test]
    fn test_new_rejects_infinity_in_normal() {
        let (mut normals, heights) = tesseract_hrep();
        normals[0] = Vector4::new(f64::INFINITY, 0.0, 0.0, 0.0);

        let result = HRep::new(normals, heights);
        assert!(matches!(
            result,
            Err(HRepError::InvalidCoordinate {
                field: "normal",
                index: 0,
                ..
            })
        ));
    }

    #[test]
    fn test_new_rejects_nan_in_height() {
        let (normals, mut heights) = tesseract_hrep();
        heights[3] = f64::NAN;

        let result = HRep::new(normals, heights);
        assert!(matches!(
            result,
            Err(HRepError::InvalidCoordinate {
                field: "height",
                index: 3,
                ..
            })
        ));
    }

    #[test]
    fn test_new_rejects_infinity_in_height() {
        let (normals, mut heights) = tesseract_hrep();
        heights[5] = f64::INFINITY;

        let result = HRep::new(normals, heights);
        assert!(matches!(
            result,
            Err(HRepError::InvalidCoordinate {
                field: "height",
                index: 5,
                ..
            })
        ));
    }

    #[test]
    fn test_new_rejects_zero_normal() {
        let (mut normals, heights) = tesseract_hrep();
        normals[1] = Vector4::zeros();

        let result = HRep::new(normals, heights);
        // Zero normal has norm 0, which fails the unit normal check
        assert!(matches!(
            result,
            Err(HRepError::NonUnitNormal { index: 1, .. })
        ));
    }

    /// This is the critical test that catches the "axis-only" bug.
    ///
    /// These normals cover all 8 axis directions (±e₁, ±e₂, ±e₃, ±e₄),
    /// but do NOT positively span R⁴. The polytope is unbounded in direction (1,1,1,1).
    #[test]
    fn test_new_rejects_unbounded_despite_covering_axes() {
        // Direction we want to be uncovered: v = (1,1,1,1)/2
        // All normals have ⟨n, v⟩ ≤ 0
        let normals = vec![
            // Each normal covers one +eᵢ axis but has negative sum
            Vector4::new(1.0, -1.0, -1.0, -1.0).normalize(),
            Vector4::new(-1.0, 1.0, -1.0, -1.0).normalize(),
            Vector4::new(-1.0, -1.0, 1.0, -1.0).normalize(),
            Vector4::new(-1.0, -1.0, -1.0, 1.0).normalize(),
            // Covers all -eᵢ axes
            Vector4::new(-1.0, -1.0, -1.0, -1.0).normalize(),
        ];
        let heights = vec![1.0; 5];

        // Verify test setup: all axis directions are covered
        for axis in 0..4 {
            assert!(
                normals.iter().any(|n| n[axis] > 0.1),
                "should cover +e{} axis",
                axis
            );
            assert!(
                normals.iter().any(|n| n[axis] < -0.1),
                "should cover -e{} axis",
                axis
            );
        }

        // But the polytope is unbounded in direction (1,1,1,1)!
        let result = HRep::new(normals, heights);
        assert!(
            matches!(result, Err(HRepError::Unbounded)),
            "should detect unboundedness despite covering all axis directions"
        );
    }
}
