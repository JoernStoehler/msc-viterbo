//! Placeholder algorithm crate so pipelines stay warm until real code lands.
//! Demonstrates minimal stubs using `rust_viterbo_geom`.

use rust_viterbo_geom::{omega, Polytope4H, SymplecticVector};

#[derive(Debug, Clone)]
pub struct CapacityResult {
    pub capacity: f64,
}

#[derive(Debug, Clone)]
pub struct AlgorithmStubError {
    pub message: String,
}

impl std::fmt::Display for AlgorithmStubError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for AlgorithmStubError {}

pub fn compute_capacity_stub(_polytope: &Polytope4H) -> Result<CapacityResult, AlgorithmStubError> {
    Err(AlgorithmStubError {
        message: "tube algorithm not implemented".to_string(),
    })
}

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
        acc += omega(a, b).abs();
        count += 1;
    }
    Some(acc / (count as f64))
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
            SymplecticVector::new(0.0, 1.0, 0.0, 0.0), // form = 0
        ];
        let avg = average_pair_capacity(&pts).unwrap();
        assert!((avg - 0.5).abs() < 1e-12);
    }
}
