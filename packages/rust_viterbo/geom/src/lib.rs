//! Core symplectic geometry structures and operations for the Viterbo project.
//!
//! This crate provides:
//! - Type aliases for 4D symplectic vectors and matrices
//! - Symplectic algebra (J, ω, trivialization, transition matrices, rotation numbers)
//! - Polytope H-representation and 2-face enumeration
//! - Lagrangian detection and perturbation utilities
//!
//! Conventions (locked): coordinates (q₁, q₂, p₁, p₂) and J(q,p) = (-p, q).

pub mod perturbation;
pub mod polytope;
pub mod symplectic;
pub mod types;

// Re-export main API
pub use perturbation::{
    detect_near_lagrangian, perturb_polytope_normals, LagrangianDetection, LagrangianWitness,
    PerturbationMetadata, PerturbationOutcome,
};
pub use polytope::{PolytopeHRep, PolytopeValidationError, TwoFace};
pub use symplectic::{
    apply_j, classify_sp2, quaternion, rotation_number, symplectic_form, symplectic_form_2d,
    transition_matrix, trivialization, two_face_rotation, Sp2Class,
};
pub use types::{Matrix2f, Matrix4f, SymplecticVector, Vector2f, Vector4f};
