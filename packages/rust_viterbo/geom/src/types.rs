//! Type aliases for symplectic geometry in ℝ⁴.
//!
//! Coordinates follow the convention (q₁, q₂, p₁, p₂).

use nalgebra::{Matrix2, Matrix4, Vector2, Vector4};

pub type Vector4f = Vector4<f64>;
pub type Vector2f = Vector2<f64>;
pub type Matrix4f = Matrix4<f64>;
pub type Matrix2f = Matrix2<f64>;

/// A vector in ℝ⁴ with symplectic structure.
pub type SymplecticVector = Vector4f;
