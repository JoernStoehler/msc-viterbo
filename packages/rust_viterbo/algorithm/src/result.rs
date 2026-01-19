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
