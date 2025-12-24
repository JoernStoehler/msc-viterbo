//! Placeholder algorithm crate so pipelines stay warm until real code lands.
//! Demonstrates a trivial computation using `rust_viterbo_geom`.

use rust_viterbo_geom::{
    symplectic_form, LagrangianDetection, PerturbationMetadata, PolytopeHRep, SymplecticVector,
};

#[derive(Clone, Debug)]
pub struct CapacityDiagnostics {
    pub eps_lagr: f64,
    pub lagrangian_detection: LagrangianDetection,
    pub perturbation: Option<PerturbationMetadata>,
}

#[derive(Clone, Debug)]
pub struct CapacityResult {
    pub capacity: f64,
}

#[derive(Clone, Debug)]
pub enum AlgorithmError {
    NotImplemented { diagnostics: CapacityDiagnostics },
}

/// Stub for the tube-based capacity algorithm (H-rep only).
pub fn tube_capacity_hrep(
    _polytope: &PolytopeHRep,
    diagnostics: CapacityDiagnostics,
) -> Result<CapacityResult, AlgorithmError> {
    Err(AlgorithmError::NotImplemented { diagnostics })
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
        acc += symplectic_form(a, b).abs();
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
            SymplecticVector::new(0.0, 0.0, 1.0, 0.0), // omega = 1 with previous
            SymplecticVector::new(0.0, 1.0, 0.0, 0.0), // omega = 0 with previous
        ];
        assert_eq!(average_pair_capacity(&pts), Some(0.5));
    }
}
