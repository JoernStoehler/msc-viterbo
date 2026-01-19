//! Lagrangian detection and perturbation for polytopes.
//!
//! A 2-face Fᵢ ∩ Fⱼ is Lagrangian if ω(nᵢ, nⱼ) = 0. Lagrangian 2-faces are
//! problematic for the algorithm because the transition matrix is singular.
//! We detect and perturb to avoid them.

use crate::polytope::PolytopeHRep;
use crate::symplectic::symplectic_form;
use crate::types::SymplecticVector;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

/// Witness for a near-Lagrangian 2-face.
#[derive(Clone, Copy, Debug)]
pub struct LagrangianWitness {
    /// Index of first facet.
    pub i: usize,
    /// Index of second facet.
    pub j: usize,
    /// Symplectic form value ω(nᵢ, nⱼ).
    pub omega: f64,
}

/// Result of Lagrangian detection.
#[derive(Clone, Copy, Debug)]
pub struct LagrangianDetection {
    /// True if a near-Lagrangian 2-face was found.
    pub detected: bool,
    /// Threshold used for detection.
    pub eps_lagr: f64,
    /// Witness (if detected).
    pub witness: Option<LagrangianWitness>,
}

/// Detect if any 2-face is near-Lagrangian.
///
/// A 2-face (i, j) is near-Lagrangian if |ω(nᵢ, nⱼ)| ≤ eps_lagr.
pub fn detect_near_lagrangian(
    polytope: &PolytopeHRep,
    eps_lagr: f64,
    eps_feas: f64,
    eps_dedup: f64,
) -> LagrangianDetection {
    for face in polytope.two_faces(eps_feas, eps_dedup) {
        let omega = symplectic_form(polytope.normals[face.i], polytope.normals[face.j]);
        if omega.abs() <= eps_lagr {
            return LagrangianDetection {
                detected: true,
                eps_lagr,
                witness: Some(LagrangianWitness {
                    i: face.i,
                    j: face.j,
                    omega,
                }),
            };
        }
    }
    LagrangianDetection {
        detected: false,
        eps_lagr,
        witness: None,
    }
}

/// Metadata about a perturbation operation.
#[derive(Clone, Copy, Debug)]
pub struct PerturbationMetadata {
    /// RNG seed used.
    pub seed: u64,
    /// Perturbation magnitude.
    pub epsilon: f64,
    /// Number of normals perturbed.
    pub perturbed_count: usize,
}

/// Result of perturbing a polytope.
#[derive(Clone, Debug)]
pub struct PerturbationOutcome {
    /// The perturbed polytope.
    pub polytope: PolytopeHRep,
    /// Metadata about the perturbation.
    pub metadata: PerturbationMetadata,
}

/// Perturb all normals of a polytope by a small random amount.
///
/// Uses deterministic RNG with the given seed for reproducibility.
pub fn perturb_polytope_normals(
    polytope: &PolytopeHRep,
    seed: u64,
    epsilon: f64,
) -> PerturbationOutcome {
    if epsilon == 0.0 {
        return PerturbationOutcome {
            polytope: polytope.clone(),
            metadata: PerturbationMetadata {
                seed,
                epsilon,
                perturbed_count: 0,
            },
        };
    }

    let mut rng = StdRng::seed_from_u64(seed);
    let mut new_normals = Vec::with_capacity(polytope.normals.len());
    for normal in &polytope.normals {
        let mut delta = SymplecticVector::new(
            rng.gen_range(-1.0..1.0),
            rng.gen_range(-1.0..1.0),
            rng.gen_range(-1.0..1.0),
            rng.gen_range(-1.0..1.0),
        );
        if delta.norm() <= f64::EPSILON {
            delta = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        }
        let perturbed = (normal + delta.scale(epsilon)).normalize();
        new_normals.push(perturbed);
    }

    PerturbationOutcome {
        polytope: PolytopeHRep::new(new_normals, polytope.heights.clone()),
        metadata: PerturbationMetadata {
            seed,
            epsilon,
            perturbed_count: polytope.normals.len(),
        },
    }
}
