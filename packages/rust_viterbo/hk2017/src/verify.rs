//! Result verification for the HK2017 algorithm.
//!
//! Verifies that computed results satisfy all required constraints and
//! the capacity formula is correctly applied.

use nalgebra::Vector4;

use crate::solve::compute_q_global;
use crate::types::{FacetData, Hk2017Result, CONSTRAINT_TOL, EPS, POSITIVE_TOL};

/// Verification error with detailed diagnostics.
#[derive(Debug)]
pub struct VerificationError {
    pub message: String,
    pub details: VerificationDetails,
}

/// Details about what failed verification.
#[derive(Debug)]
pub enum VerificationDetails {
    /// A beta coefficient is negative.
    NegativeBeta { index: usize, value: f64 },
    /// Height constraint violated.
    HeightConstraint { expected: f64, actual: f64 },
    /// Closure constraint violated.
    ClosureConstraint { norm: f64 },
    /// Q value mismatch.
    QMismatch { expected: f64, actual: f64 },
    /// Capacity formula mismatch.
    CapacityMismatch { expected: f64, actual: f64 },
    /// Q value is non-positive.
    NonPositiveQ { value: f64 },
}

impl std::fmt::Display for VerificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {:?}", self.message, self.details)
    }
}

impl std::error::Error for VerificationError {}

impl Hk2017Result {
    /// Verify the result satisfies all constraints.
    ///
    /// In debug builds, panics on verification failure.
    /// In release builds, this is a no-op unless called explicitly.
    pub fn verify(&self, facet_data: &FacetData) {
        if cfg!(debug_assertions) {
            if let Err(e) = self.verify_checked(facet_data) {
                panic!("HK2017 result verification failed: {}", e);
            }
        }
    }

    /// Verify the result and return detailed error on failure.
    pub fn verify_checked(&self, facet_data: &FacetData) -> Result<(), VerificationError> {
        self.verify_beta_nonnegative()?;
        self.verify_height_constraint(facet_data)?;
        self.verify_closure_constraint(facet_data)?;
        self.verify_q_value(facet_data)?;
        self.verify_capacity_formula()?;
        Ok(())
    }

    /// Check that all beta coefficients are non-negative.
    fn verify_beta_nonnegative(&self) -> Result<(), VerificationError> {
        for (i, &beta) in self.optimal_beta.iter().enumerate() {
            if beta < -POSITIVE_TOL {
                return Err(VerificationError {
                    message: format!("beta[{}] = {} is negative", i, beta),
                    details: VerificationDetails::NegativeBeta {
                        index: i,
                        value: beta,
                    },
                });
            }
        }
        Ok(())
    }

    /// Check that the height constraint is satisfied: Sum beta_i h_i = 1.
    fn verify_height_constraint(&self, facet_data: &FacetData) -> Result<(), VerificationError> {
        let height_sum: f64 = self
            .optimal_beta
            .iter()
            .zip(&facet_data.heights)
            .map(|(&b, &h)| b * h)
            .sum();

        if (height_sum - 1.0).abs() > CONSTRAINT_TOL {
            return Err(VerificationError {
                message: format!("Height sum = {} != 1", height_sum),
                details: VerificationDetails::HeightConstraint {
                    expected: 1.0,
                    actual: height_sum,
                },
            });
        }
        Ok(())
    }

    /// Check that the closure constraint is satisfied: Sum beta_i n_i = 0.
    fn verify_closure_constraint(&self, facet_data: &FacetData) -> Result<(), VerificationError> {
        let mut closure = Vector4::zeros();
        for (&beta, normal) in self.optimal_beta.iter().zip(&facet_data.normals) {
            closure += normal * beta;
        }

        let norm = closure.norm();
        if norm > CONSTRAINT_TOL {
            return Err(VerificationError {
                message: format!("Closure norm = {} != 0", norm),
                details: VerificationDetails::ClosureConstraint { norm },
            });
        }
        Ok(())
    }

    /// Check that the stored Q value matches recomputation.
    fn verify_q_value(&self, facet_data: &FacetData) -> Result<(), VerificationError> {
        let q_computed =
            compute_q_global(&self.optimal_beta, &self.optimal_permutation, facet_data);

        if (q_computed - self.q_max).abs() > EPS {
            return Err(VerificationError {
                message: format!(
                    "Q mismatch: computed {} vs stored {}",
                    q_computed, self.q_max
                ),
                details: VerificationDetails::QMismatch {
                    expected: self.q_max,
                    actual: q_computed,
                },
            });
        }

        if self.q_max <= 0.0 {
            return Err(VerificationError {
                message: format!("Q = {} is not positive", self.q_max),
                details: VerificationDetails::NonPositiveQ { value: self.q_max },
            });
        }

        Ok(())
    }

    /// Check that the capacity formula is correctly applied: c = 1/(2Q).
    fn verify_capacity_formula(&self) -> Result<(), VerificationError> {
        let expected_capacity = 1.0 / (2.0 * self.q_max);
        if (self.capacity - expected_capacity).abs() > EPS {
            return Err(VerificationError {
                message: format!(
                    "Capacity mismatch: stored {} vs computed {}",
                    self.capacity, expected_capacity
                ),
                details: VerificationDetails::CapacityMismatch {
                    expected: expected_capacity,
                    actual: self.capacity,
                },
            });
        }
        Ok(())
    }
}

/// Verify that two results are equivalent (for comparing enumeration strategies).
pub fn verify_results_equivalent(
    result1: &Hk2017Result,
    result2: &Hk2017Result,
    tolerance: f64,
) -> Result<(), String> {
    let diff = (result1.capacity - result2.capacity).abs();
    if diff > tolerance {
        return Err(format!(
            "Capacity mismatch: {} vs {} (diff = {})",
            result1.capacity, result2.capacity, diff
        ));
    }

    let q_diff = (result1.q_max - result2.q_max).abs();
    if q_diff > tolerance {
        return Err(format!(
            "Q_max mismatch: {} vs {} (diff = {})",
            result1.q_max, result2.q_max, q_diff
        ));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::PolytopeHRep;
    use nalgebra::Vector4;

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
    fn test_verify_valid_result() {
        // Instead of manually constructing a result, run the algorithm
        // and verify the actual output passes verification
        use crate::{hk2017_capacity, Hk2017Config};

        let polytope = make_tesseract();
        let facet_data = FacetData::from_polytope(&polytope).unwrap();
        let config = Hk2017Config::default();

        let result = hk2017_capacity(&polytope, &config).unwrap();

        // The algorithm result should pass verification
        let verify_result = result.verify_checked(&facet_data);
        assert!(
            verify_result.is_ok(),
            "Verification failed: {:?}",
            verify_result
        );

        // Also verify the capacity is correct
        assert!((result.capacity - 4.0).abs() < 1e-6);
    }

    #[test]
    fn test_verify_negative_beta_fails() {
        let polytope = make_tesseract();
        let facet_data = FacetData::from_polytope(&polytope).unwrap();

        let result = Hk2017Result {
            capacity: 4.0,
            optimal_permutation: vec![0, 4, 1, 5],
            optimal_beta: vec![-0.1, 0.3, 0.0, 0.0, 0.25, 0.25, 0.0, 0.0], // Negative beta
            q_max: 0.125,
            permutations_evaluated: 100,
            permutations_rejected: 50,
            interior_only_assumption: true,
        };

        let verify_result = result.verify_checked(&facet_data);
        assert!(verify_result.is_err());
    }

    #[test]
    fn test_verify_height_constraint_fails() {
        let polytope = make_tesseract();
        let facet_data = FacetData::from_polytope(&polytope).unwrap();

        let result = Hk2017Result {
            capacity: 4.0,
            optimal_permutation: vec![0, 4, 1, 5],
            optimal_beta: vec![0.1, 0.1, 0.0, 0.0, 0.1, 0.1, 0.0, 0.0], // Sum = 0.4, not 1
            q_max: 0.125,
            permutations_evaluated: 100,
            permutations_rejected: 50,
            interior_only_assumption: true,
        };

        let verify_result = result.verify_checked(&facet_data);
        assert!(verify_result.is_err());
        if let Err(e) = verify_result {
            assert!(matches!(
                e.details,
                VerificationDetails::HeightConstraint { .. }
            ));
        }
    }
}
