//! 4D convex geometry primitives for symplectic capacity algorithms.
//!
//! This crate provides foundational types and operations for 4D convex polytopes,
//! used by EHZ capacity algorithms (HK2017, Tube, Billiard).
//!
//! # Types
//!
//! - [`HRep`]: H-representation (half-space intersection) of a 4D polytope
//!
//! # Functions
//!
//! - [`is_bounded`]: Check if normals positively span ℝ⁴ (polytope is bounded)
//!
//! # Design Principles
//!
//! 1. **Validated types**: [`HRep::new`] validates all invariants; invalid input is rejected.
//! 2. **Documented proofs**: Each function has a correctness proof in its doc-comment.
//! 3. **Comprehensive tests**: Both positive (valid input accepted) and negative (invalid rejected) cases.
//! 4. **No silent failures**: Invalid input returns specific errors, not garbage results.
//!
//! # Mathematical Background
//!
//! A 4D polytope K with 0 ∈ int(K) is represented as:
//!
//! ```text
//! K = ⋂ᵢ { x ∈ ℝ⁴ : ⟨nᵢ, x⟩ ≤ hᵢ }
//! ```
//!
//! where nᵢ are outward unit normals and hᵢ > 0 are heights.
//!
//! # Example
//!
//! ```
//! use nalgebra::Vector4;
//! use geom4d::HRep;
//!
//! // Unit tesseract [-1, 1]⁴
//! let normals = vec![
//!     Vector4::new(1.0, 0.0, 0.0, 0.0),
//!     Vector4::new(-1.0, 0.0, 0.0, 0.0),
//!     Vector4::new(0.0, 1.0, 0.0, 0.0),
//!     Vector4::new(0.0, -1.0, 0.0, 0.0),
//!     Vector4::new(0.0, 0.0, 1.0, 0.0),
//!     Vector4::new(0.0, 0.0, -1.0, 0.0),
//!     Vector4::new(0.0, 0.0, 0.0, 1.0),
//!     Vector4::new(0.0, 0.0, 0.0, -1.0),
//! ];
//! let heights = vec![1.0; 8];
//!
//! let tesseract = HRep::new(normals, heights).expect("valid H-rep");
//! assert_eq!(tesseract.num_facets(), 8);
//! ```

pub mod bounded;
pub mod hrep;
pub mod tolerances;

pub use bounded::is_bounded;
pub use hrep::{HRep, HRepError};
pub use tolerances::{EPS, EPS_HEIGHT, EPS_UNIT, MAX_COORD};
