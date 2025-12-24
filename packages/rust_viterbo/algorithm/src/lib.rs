//! Placeholder algorithm crate so pipelines stay warm until real code lands.
//! Demonstrates a trivial computation using `rust_viterbo_geom`.

use rust_viterbo_geom::{symplectic_form, Polytope4HRep, SymplecticVector};

/// Compute a toy “capacity estimate” by summing absolute symplectic forms
/// over consecutive pairs and averaging.
pub fn average_pair_capacity(points: &[SymplecticVector]) -> Option<f64> {
    if points.len() < 2 {
        return None;
    }
    let mut acc = 0.0;
    let mut count = 0;
    for pair in points.windows(2) {
        let a = pair[0];
        let b = pair[1];
        acc += symplectic_form(a, b).abs();
        count += 1;
    }
    Some(acc / (count as f64))
}

/// Placeholder for the tube capacity algorithm (H-rep only).
pub fn tube_capacity_hrep(_hrep: &Polytope4HRep) -> Result<f64, AlgorithmError> {
    Err(AlgorithmError::NotImplemented)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AlgorithmError {
    NotImplemented,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn returns_none_for_too_few_points() {
        assert_eq!(average_pair_capacity(&[]), None);
        assert_eq!(
            average_pair_capacity(&[SymplecticVector::new(1.0, 0.0, 0.0, 0.0)]),
            None
        );
    }

    #[test]
    fn computes_average_capacity() {
        let pts = [
            SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
            SymplecticVector::new(0.0, 0.0, 1.0, 0.0), // form = 1
            SymplecticVector::new(-1.0, 0.0, 0.0, 0.0), // form = 1
        ];
        assert_eq!(average_pair_capacity(&pts), Some(1.0));
    }
}
