//! Core symplectic geometry structures and operations for the Viterbo project.
//!
//! The crate currently exposes light-weight placeholder types so we can
//! validate the toolchain end-to-end before dropping in the real math.

use nalgebra::Vector2;

/// Simple 2D vector tailored to quick symplectic-form experiments.
pub type SymplecticVector = Vector2<f64>;

/// Compute the standard symplectic form ⟨v, w⟩ = x₁y₂ - y₁x₂.
pub fn symplectic_form(v: SymplecticVector, w: SymplecticVector) -> f64 {
    v.x * w.y - v.y * w.x
}

#[cfg(test)]
mod tests {
    use super::{symplectic_form, SymplecticVector};

    #[test]
    fn symplectic_form_matches_cross_product() {
        let v = SymplecticVector::new(1.0, 2.0);
        let w = SymplecticVector::new(3.0, -1.0);

        assert_eq!(symplectic_form(v, w), -7.0);
        assert_eq!(symplectic_form(w, v), 7.0);
    }
}
