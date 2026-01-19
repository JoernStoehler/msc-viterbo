//! Tests for known capacity values from literature.
//!
//! Each test should cite its source.

use crate::compute::{CapacityAlgorithm, MinkowskiBilliardAlgorithm};
use super::fixtures::tesseract;

/// Tesseract capacity is 4.0.
///
/// Source: Well-known result. The tesseract B² × B² = [-1,1]² × [-1,1]² has
/// c_EHZ = 4 · Area(B²) / perimeter(B²) · 2 = 4 · 4 / 8 · 2 = 4.
/// (The formula c_EHZ(K₁ × K₂) = 2 · width(K₁) · width(K₂) gives 2 · 2 · 2 = 8,
/// but that's for the Minkowski billiard action, which equals capacity for squares.)
///
/// TODO: Find proper citation. Candidates: Haim-Kislev 2017, Rudolf 2022.
#[test]
fn tesseract_capacity_is_four() {
    let algo = MinkowskiBilliardAlgorithm::new();
    let result = algo.compute(tesseract()).expect("billiard should succeed");

    assert!(
        (result.capacity - 4.0).abs() < 1e-6,
        "tesseract capacity should be 4.0, got {}",
        result.capacity
    );
}
