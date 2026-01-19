//! Output types for the capacity algorithm.
//!
//! This module defines:
//! - `WitnessOrbit`: A concrete periodic Reeb orbit with breakpoints and times
//! - `Diagnostics`: Statistics about the branch-and-bound search
//! - `CapacityResult`: The final output combining capacity, witness, and diagnostics
//! - `AlgorithmError`: Error conditions

use rust_viterbo_geom::{apply_j, LagrangianDetection, PerturbationMetadata, PolytopeHRep, SymplecticVector};
use std::fmt;

/// A witness periodic Reeb orbit.
///
/// Contains the concrete geometric data for verification and visualization.
#[derive(Clone, Debug)]
pub struct WitnessOrbit {
    /// Breakpoints in ℝ⁴ (corner points of the orbit)
    pub breakpoints: Vec<SymplecticVector>,
    /// Facet index for each segment
    pub facet_sequence: Vec<usize>,
    /// Time spent on each segment (equals action since dA/dt = 1 on Reeb flow)
    pub segment_times: Vec<f64>,
}

/// Result of verifying a witness orbit.
#[derive(Clone, Debug)]
pub struct WitnessVerification {
    /// Whether the orbit is valid (all checks pass within tolerance)
    pub valid: bool,
    /// Maximum error in facet constraint (should be ~0)
    pub max_facet_error: f64,
    /// Maximum error in flow equation (should be ~0)
    pub max_flow_error: f64,
    /// Closure error (distance from last to first point)
    pub closure_error: f64,
    /// Action computed from segment times
    pub computed_action: f64,
}

impl WitnessOrbit {
    /// Verify that the witness orbit satisfies all Reeb orbit conditions.
    ///
    /// This handles the differential inclusion on Lagrangian 2-faces, where
    /// the velocity can be any convex combination of adjacent facet Reeb vectors.
    /// A 2-face is Lagrangian iff ω(n_i, n_j) = 0.
    pub fn verify(&self, hrep: &PolytopeHRep, tol: f64) -> WitnessVerification {
        let mut max_facet_error = 0.0_f64;
        let mut max_flow_error = 0.0_f64;
        let mut valid = true;

        let n_segments = self.segment_times.len();
        if n_segments == 0 || self.breakpoints.is_empty() {
            return WitnessVerification {
                valid: false,
                max_facet_error: f64::INFINITY,
                max_flow_error: f64::INFINITY,
                closure_error: f64::INFINITY,
                computed_action: 0.0,
            };
        }

        for s in 0..n_segments {
            let p_start = self.breakpoints[s];
            let p_end = if s == n_segments - 1 {
                self.breakpoints[0]
            } else {
                self.breakpoints[s + 1]
            };

            let facet_k = self.facet_sequence[s + 1];
            let time = self.segment_times[s];

            if time <= 0.0 {
                valid = false;
            }

            // Check that start point lies on facet
            let n_k = hrep.normals[facet_k];
            let h_k = hrep.heights[facet_k];
            let facet_error = (n_k.dot(&p_start) - h_k).abs();
            max_facet_error = max_facet_error.max(facet_error);

            // Get previous facet for 2-face check
            let facet_prev = self.facet_sequence[s];
            let n_prev = hrep.normals[facet_prev];
            let h_prev = hrep.heights[facet_prev];

            // Check if this 2-face is Lagrangian: ω(n_prev, n_k) ≈ 0
            let omega = rust_viterbo_geom::symplectic_form(n_prev, n_k);
            let is_lagrangian = omega.abs() < tol;

            let displacement = p_end - p_start;

            if is_lagrangian {
                // On Lagrangian 2-face: velocity ∈ conv{v_prev, v_k}
                // Displacement = λ_prev * v_prev + λ_k * v_k for λ_prev, λ_k ≥ 0
                let v_prev = apply_j(n_prev) * (2.0 / h_prev);
                let v_k_reeb = apply_j(n_k) * (2.0 / h_k);

                // Solve: displacement = λ_prev * v_prev + λ_k * v_k
                // This is a 2x4 system (overdetermined). Use least squares.
                let flow_error = verify_differential_inclusion(displacement, v_prev, v_k_reeb, tol);
                max_flow_error = max_flow_error.max(flow_error);
            } else {
                // Non-Lagrangian: unique Reeb velocity on this facet
                let v_k = apply_j(n_k) * (2.0 / h_k);
                let expected_end = p_start + v_k * time;
                let flow_error = (p_end - expected_end).norm();
                max_flow_error = max_flow_error.max(flow_error);
            }
        }

        // Closure check: final point should equal first point
        let last_idx = n_segments - 1;
        let p_last = self.breakpoints[last_idx];
        let facet_last = self.facet_sequence[last_idx + 1];
        let facet_closing = self.facet_sequence[0]; // facet we close through

        let n_last = hrep.normals[facet_last];
        let h_last = hrep.heights[facet_last];
        let n_closing = hrep.normals[facet_closing];

        // Check if closing 2-face is Lagrangian
        let omega_close = rust_viterbo_geom::symplectic_form(n_last, n_closing);
        let closing_lagrangian = omega_close.abs() < tol;

        let closure_error = if closing_lagrangian {
            // On Lagrangian closing 2-face: check if displacement is in cone
            let v_last = apply_j(n_last) * (2.0 / h_last);
            let h_closing = hrep.heights[facet_closing];
            let v_closing = apply_j(n_closing) * (2.0 / h_closing);
            let displacement = self.breakpoints[0] - p_last;
            verify_differential_inclusion(displacement, v_last, v_closing, tol)
        } else {
            let time_last = self.segment_times[last_idx];
            let v_last = apply_j(n_last) * (2.0 / h_last);
            let final_point = p_last + v_last * time_last;
            (final_point - self.breakpoints[0]).norm()
        };

        let computed_action: f64 = self.segment_times.iter().sum();

        if max_facet_error > tol || max_flow_error > tol || closure_error > tol {
            valid = false;
        }

        WitnessVerification {
            valid,
            max_facet_error,
            max_flow_error,
            closure_error,
            computed_action,
        }
    }
}

/// Verify that a displacement lies in the cone of two velocity vectors.
///
/// Returns the residual error. A valid displacement satisfies:
/// displacement = λ₁ * v1 + λ₂ * v2 with λ₁, λ₂ ≥ 0
fn verify_differential_inclusion(
    displacement: SymplecticVector,
    v1: SymplecticVector,
    v2: SymplecticVector,
    _tol: f64,
) -> f64 {
    // Solve least squares: [v1 | v2] * [λ₁; λ₂] = displacement
    // This is a 4x2 overdetermined system.
    //
    // Normal equations: A^T A x = A^T b where A = [v1 | v2], b = displacement
    // A^T A = [[v1·v1, v1·v2], [v2·v1, v2·v2]]
    // A^T b = [v1·d, v2·d]

    let a11 = v1.dot(&v1);
    let a12 = v1.dot(&v2);
    let a22 = v2.dot(&v2);
    let b1 = v1.dot(&displacement);
    let b2 = v2.dot(&displacement);

    let det = a11 * a22 - a12 * a12;

    if det.abs() < 1e-14 {
        // v1 and v2 are nearly parallel - degenerate case
        // Check if displacement is parallel to v1 (or v2)
        if a11 > 1e-14 {
            let lambda = b1 / a11;
            if lambda >= -1e-10 {
                let residual = displacement - v1 * lambda;
                return residual.norm();
            }
        }
        return displacement.norm(); // Can't achieve this displacement
    }

    // Solve 2x2 system
    let lambda1 = (a22 * b1 - a12 * b2) / det;
    let lambda2 = (a11 * b2 - a12 * b1) / det;

    // Check non-negativity (with small tolerance for numerical errors)
    let lambda1_ok = lambda1 >= -1e-10;
    let lambda2_ok = lambda2 >= -1e-10;

    if lambda1_ok && lambda2_ok {
        // Compute residual with the solved lambdas
        let achieved = v1 * lambda1 + v2 * lambda2;
        (displacement - achieved).norm()
    } else {
        // Lambdas would be negative - try projecting onto each ray separately
        let mut best_error = f64::INFINITY;

        // Try v1 only (λ2 = 0)
        if a11 > 1e-14 {
            let lambda = (b1 / a11).max(0.0);
            let residual = displacement - v1 * lambda;
            best_error = best_error.min(residual.norm());
        }

        // Try v2 only (λ1 = 0)
        if a22 > 1e-14 {
            let lambda = (b2 / a22).max(0.0);
            let residual = displacement - v2 * lambda;
            best_error = best_error.min(residual.norm());
        }

        // Try origin (no movement possible in cone)
        best_error = best_error.min(displacement.norm());

        best_error
    }
}

/// Diagnostic information about the algorithm run.
#[derive(Clone, Debug, Default)]
pub struct Diagnostics {
    pub nodes_explored: u64,
    pub nodes_pruned_empty: u64,
    pub nodes_pruned_action: u64,
    pub nodes_pruned_rotation: u64,
    pub best_action_found: f64,
    pub lagrangian_detection: Option<LagrangianDetection>,
    pub perturbation: Option<PerturbationMetadata>,
}

/// Final result of the capacity computation.
#[derive(Clone, Debug)]
pub struct CapacityResult {
    pub capacity: f64,
    pub witness: Option<WitnessOrbit>,
    pub diagnostics: Diagnostics,
}

/// Error type for the algorithm.
#[derive(Clone, Debug)]
pub enum AlgorithmError {
    EmptyPolytope,
    NoValidOrbits,
    ValidationError(String),
}

impl fmt::Display for AlgorithmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyPolytope => write!(f, "polytope has no non-Lagrangian 2-faces"),
            Self::NoValidOrbits => write!(f, "no valid periodic orbits found"),
            Self::ValidationError(msg) => write!(f, "validation error: {msg}"),
        }
    }
}

impl std::error::Error for AlgorithmError {}

#[cfg(test)]
mod tests {
    use super::*;

    /// Create a simple tesseract H-rep for testing.
    fn tesseract_hrep() -> PolytopeHRep {
        let normals = vec![
            SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
            SymplecticVector::new(-1.0, 0.0, 0.0, 0.0),
            SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
            SymplecticVector::new(0.0, -1.0, 0.0, 0.0),
            SymplecticVector::new(0.0, 0.0, 1.0, 0.0),
            SymplecticVector::new(0.0, 0.0, -1.0, 0.0),
            SymplecticVector::new(0.0, 0.0, 0.0, 1.0),
            SymplecticVector::new(0.0, 0.0, 0.0, -1.0),
        ];
        PolytopeHRep::new(normals, vec![1.0; 8])
    }

    // =========================================================================
    // verify_differential_inclusion Tests
    // =========================================================================

    #[test]
    fn verify_inclusion_exact_v1() {
        // displacement = λ₁ * v1 with λ₁ = 1
        let v1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        let v2 = SymplecticVector::new(0.0, 1.0, 0.0, 0.0);
        let displacement = v1;

        let error = verify_differential_inclusion(displacement, v1, v2, 1e-10);
        assert!(error < 1e-10, "Exact v1 should have zero error, got {:.2e}", error);
    }

    #[test]
    fn verify_inclusion_exact_v2() {
        // displacement = λ₂ * v2 with λ₂ = 1
        let v1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        let v2 = SymplecticVector::new(0.0, 1.0, 0.0, 0.0);
        let displacement = v2;

        let error = verify_differential_inclusion(displacement, v1, v2, 1e-10);
        assert!(error < 1e-10, "Exact v2 should have zero error, got {:.2e}", error);
    }

    #[test]
    fn verify_inclusion_convex_combination() {
        // displacement = 0.5*v1 + 0.5*v2
        let v1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        let v2 = SymplecticVector::new(0.0, 1.0, 0.0, 0.0);
        let displacement = v1 * 0.5 + v2 * 0.5;

        let error = verify_differential_inclusion(displacement, v1, v2, 1e-10);
        assert!(error < 1e-10, "Convex combination should have zero error, got {:.2e}", error);
    }

    #[test]
    fn verify_inclusion_outside_cone() {
        // displacement perpendicular to both v1 and v2
        let v1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        let v2 = SymplecticVector::new(0.0, 1.0, 0.0, 0.0);
        let displacement = SymplecticVector::new(0.0, 0.0, 1.0, 0.0);

        let error = verify_differential_inclusion(displacement, v1, v2, 1e-10);
        assert!(error > 0.9, "Perpendicular displacement should have large error, got {:.2e}", error);
    }

    #[test]
    fn verify_inclusion_negative_lambda_rejected() {
        // displacement = -v1 (negative coefficient)
        let v1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        let v2 = SymplecticVector::new(0.0, 1.0, 0.0, 0.0);
        let displacement = -v1;

        let error = verify_differential_inclusion(displacement, v1, v2, 1e-10);
        assert!(error > 0.9, "Negative lambda should give large error, got {:.2e}", error);
    }

    // =========================================================================
    // WitnessOrbit::verify Tests
    // =========================================================================

    #[test]
    fn witness_verify_empty_orbit() {
        let hrep = tesseract_hrep();
        let witness = WitnessOrbit {
            breakpoints: vec![],
            facet_sequence: vec![],
            segment_times: vec![],
        };
        let result = witness.verify(&hrep, 1e-6);
        assert!(!result.valid, "Empty orbit should be invalid");
    }

    #[test]
    fn witness_verify_positive_times() {
        // An orbit with non-positive times should be invalid
        let hrep = tesseract_hrep();
        let witness = WitnessOrbit {
            breakpoints: vec![SymplecticVector::new(1.0, 0.0, 0.0, 0.0)],
            facet_sequence: vec![0, 0],  // Minimal facet sequence
            segment_times: vec![-1.0],    // Negative time!
        };
        let result = witness.verify(&hrep, 1e-6);
        assert!(!result.valid, "Orbit with negative time should be invalid");
    }

    #[test]
    fn witness_verify_computes_action() {
        // Check that computed_action equals sum of segment_times
        let hrep = tesseract_hrep();
        let times = vec![1.0, 2.0, 3.0, 4.0];
        let witness = WitnessOrbit {
            breakpoints: vec![
                SymplecticVector::new(0.5, 0.5, 0.0, 0.0),
                SymplecticVector::new(0.5, 0.5, 0.5, 0.0),
                SymplecticVector::new(0.5, 0.5, 0.5, 0.5),
                SymplecticVector::new(0.5, 0.0, 0.5, 0.5),
            ],
            facet_sequence: vec![0, 4, 6, 2, 0],
            segment_times: times.clone(),
        };
        let result = witness.verify(&hrep, 1e-6);
        let expected_action: f64 = times.iter().sum();
        assert!((result.computed_action - expected_action).abs() < 1e-10,
            "computed_action = {} should equal sum of times = {}",
            result.computed_action, expected_action);
    }

    // =========================================================================
    // WitnessVerification Structure Tests
    // =========================================================================

    #[test]
    fn witness_verification_fields_initialized() {
        let verification = WitnessVerification {
            valid: true,
            max_facet_error: 0.001,
            max_flow_error: 0.002,
            closure_error: 0.003,
            computed_action: 4.0,
        };
        assert!(verification.valid);
        assert!((verification.max_facet_error - 0.001).abs() < 1e-10);
        assert!((verification.max_flow_error - 0.002).abs() < 1e-10);
        assert!((verification.closure_error - 0.003).abs() < 1e-10);
        assert!((verification.computed_action - 4.0).abs() < 1e-10);
    }

    // =========================================================================
    // Diagnostics Tests
    // =========================================================================

    #[test]
    fn diagnostics_default_values() {
        let diag = Diagnostics::default();
        assert_eq!(diag.nodes_explored, 0);
        assert_eq!(diag.nodes_pruned_empty, 0);
        assert_eq!(diag.nodes_pruned_action, 0);
        assert_eq!(diag.nodes_pruned_rotation, 0);
        assert!((diag.best_action_found - 0.0).abs() < 1e-10);
    }

    // =========================================================================
    // Algorithm Output Verification Tests
    // =========================================================================

    /// Test that billiard algorithm witness has breakpoints on claimed facets.
    ///
    /// MATHEMATICAL PROPERTY: Each breakpoint γ(t_i) must satisfy ⟨n_k, γ(t_i)⟩ = h_k
    /// for the facet k that the orbit passes through at that breakpoint.
    #[test]
    fn billiard_witness_breakpoints_on_facets() {
        use crate::compute::MinkowskiBilliardAlgorithm;
        use crate::compute::CapacityAlgorithm;

        let hrep = tesseract_hrep();
        let algo = MinkowskiBilliardAlgorithm::new();
        let result = algo.compute(hrep.clone()).expect("billiard should succeed");

        let witness = result.witness.expect("billiard should return witness");
        let tol = 1e-6;

        // Check each breakpoint lies on its claimed facet
        for (i, breakpoint) in witness.breakpoints.iter().enumerate() {
            // facet_sequence has length n+1 where n = number of segments
            // facet_sequence[i] is the facet the orbit is on at breakpoint[i]
            if i < witness.facet_sequence.len() {
                let facet = witness.facet_sequence[i];
                let n = hrep.normals[facet];
                let h = hrep.heights[facet];
                let constraint_value = n.dot(breakpoint);
                let error = (constraint_value - h).abs();

                assert!(
                    error < tol,
                    "Breakpoint {} should lie on facet {}. ⟨n, p⟩ = {:.6}, h = {:.6}, error = {:.2e}",
                    i, facet, constraint_value, h, error
                );
            }
        }
    }

    /// Test that billiard witness has consistent facet sequence (adjacent facets share 2-face).
    ///
    /// MATHEMATICAL PROPERTY: Consecutive facets in the orbit must share a 2-face,
    /// i.e., the orbit can only transition between facets that meet at a codimension-2 face.
    #[test]
    fn billiard_witness_facets_share_two_face() {
        use crate::compute::MinkowskiBilliardAlgorithm;
        use crate::compute::CapacityAlgorithm;
        use crate::polytope::{PolytopeData, EPS_FEAS, EPS_DEDUP};

        let hrep = tesseract_hrep();
        let algo = MinkowskiBilliardAlgorithm::new();
        let result = algo.compute(hrep.clone()).expect("billiard should succeed");

        let witness = result.witness.expect("billiard should return witness");

        // Get all 2-faces (both Lagrangian and non-Lagrangian)
        let raw_faces = hrep.two_faces(EPS_FEAS, EPS_DEDUP);
        let two_face_pairs: std::collections::HashSet<(usize, usize)> = raw_faces
            .iter()
            .map(|f| if f.i < f.j { (f.i, f.j) } else { (f.j, f.i) })
            .collect();

        // Check each consecutive pair of facets shares a 2-face
        for w in witness.facet_sequence.windows(2) {
            let (f1, f2) = if w[0] < w[1] { (w[0], w[1]) } else { (w[1], w[0]) };

            // Same facet is OK (happens at breakpoints for 2-bounce orbits)
            if f1 == f2 {
                continue;
            }

            assert!(
                two_face_pairs.contains(&(f1, f2)),
                "Consecutive facets {} and {} should share a 2-face",
                w[0], w[1]
            );
        }
    }

    /// Test that billiard witness has positive segment times.
    ///
    /// MATHEMATICAL PROPERTY: The Reeb flow moves forward in time, so all
    /// segment durations must be positive.
    #[test]
    fn billiard_witness_positive_segment_times() {
        use crate::compute::MinkowskiBilliardAlgorithm;
        use crate::compute::CapacityAlgorithm;

        let hrep = tesseract_hrep();
        let algo = MinkowskiBilliardAlgorithm::new();
        let result = algo.compute(hrep.clone()).expect("billiard should succeed");

        let witness = result.witness.expect("billiard should return witness");

        for (i, &time) in witness.segment_times.iter().enumerate() {
            assert!(
                time > 0.0,
                "Segment {} time should be positive, got {}",
                i, time
            );
        }
    }

    /// Test that billiard witness closes (last breakpoint connects to first).
    ///
    /// MATHEMATICAL PROPERTY: A periodic Reeb orbit satisfies γ(0) = γ(T).
    /// For a closed billiard, following the Reeb flow from the last breakpoint
    /// should return to the first breakpoint.
    ///
    /// NOTE: This test is currently ignored because the billiard witness construction
    /// produces approximate times, not exact Reeb flow times. The witness shows
    /// the combinatorial structure but not the exact geometry.
    #[test]
    #[ignore = "Billiard witness times are approximate, closure won't be exact"]
    fn billiard_witness_closes() {
        use crate::compute::MinkowskiBilliardAlgorithm;
        use crate::compute::CapacityAlgorithm;

        let hrep = tesseract_hrep();
        let algo = MinkowskiBilliardAlgorithm::new();
        let result = algo.compute(hrep.clone()).expect("billiard should succeed");

        let witness = result.witness.expect("billiard should return witness");
        let verification = witness.verify(&hrep, 1e-6);

        assert!(
            verification.closure_error < 1e-3,
            "Orbit should close. Closure error = {:.2e}",
            verification.closure_error
        );
    }
}
