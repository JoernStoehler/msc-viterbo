//! Core symplectic geometry structures and operations for the Viterbo project.
//!
//! The crate currently exposes light-weight placeholder types so we can
//! validate the toolchain end-to-end before dropping in the real math.

/// Simple 2D vector tailored to quick symplectic-form experiments.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SymplecticVector {
    pub x: f64,
    pub y: f64,
}

impl SymplecticVector {
    /// Construct a vector from its coordinates.
    pub const fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }

    /// Compute the standard symplectic form ⟨v, w⟩ = x₁y₂ - y₁x₂.
    pub fn symplectic_form(self, other: Self) -> f64 {
        self.x * other.y - self.y * other.x
    }
}

#[cfg(test)]
mod tests {
    use super::SymplecticVector;

    #[test]
    fn symplectic_form_matches_cross_product() {
        let v = SymplecticVector::new(1.0, 2.0);
        let w = SymplecticVector::new(3.0, -1.0);

        assert_eq!(v.symplectic_form(w), -7.0);
        assert_eq!(w.symplectic_form(v), 7.0);
    }
}
