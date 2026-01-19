//! Tests for 2D polygon operations.
//!
//! These test the random_convex_polygon generator and to_hrep_2d conversion.

use super::fixtures::random_convex_polygon;
use proptest::prelude::*;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

// ============================================================================
// Convexity and Validity Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    /// random_convex_polygon produces a valid convex polygon.
    #[test]
    fn random_polygon_is_valid_convex(seed in any::<u64>(), n in 3usize..=8) {
        let mut rng = ChaCha8Rng::seed_from_u64(seed);
        let polygon = random_convex_polygon(&mut rng, n, 0.5, 2.0);

        // Check 1: All vertices are distinct
        for i in 0..n {
            for j in (i+1)..n {
                let dist = ((polygon.vertices[i].x - polygon.vertices[j].x).powi(2)
                          + (polygon.vertices[i].y - polygon.vertices[j].y).powi(2)).sqrt();
                prop_assert!(
                    dist > 1e-10,
                    "Vertices {} and {} should be distinct, distance={:.2e}",
                    i, j, dist
                );
            }
        }

        // Check 2 & 3: CCW order and convexity via cross products
        for i in 0..n {
            let v0 = polygon.vertices[i];
            let v1 = polygon.vertices[(i + 1) % n];
            let v2 = polygon.vertices[(i + 2) % n];

            let e1 = (v1.x - v0.x, v1.y - v0.y);
            let e2 = (v2.x - v1.x, v2.y - v1.y);
            let cross = e1.0 * e2.1 - e1.1 * e2.0;

            prop_assert!(
                cross > -1e-10,
                "Polygon should be convex CCW. Edge {}: cross product = {:.6}",
                i, cross
            );
        }

        // Check 4: Origin is inside (all heights positive)
        let (_, heights) = polygon.to_hrep_2d();
        for (i, h) in heights.iter().enumerate() {
            prop_assert!(
                *h > 0.0,
                "Height {} should be positive (origin inside). h={:.6}",
                i, h
            );
        }
    }
}

// ============================================================================
// H-representation Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    /// Normals from to_hrep_2d rotate CCW around the polygon.
    #[test]
    fn to_hrep_2d_normals_are_ccw(seed in any::<u64>(), n in 3usize..=6) {
        let mut rng = ChaCha8Rng::seed_from_u64(seed);
        let polygon = random_convex_polygon(&mut rng, n, 0.5, 2.0);

        let (normals, heights) = polygon.to_hrep_2d();

        for (i, h) in heights.iter().enumerate() {
            prop_assert!(
                *h > 0.0,
                "Height {} should be positive (origin inside polygon), got {:.6}",
                i, h
            );
        }

        let angles: Vec<f64> = normals.iter().map(|n| n.y.atan2(n.x)).collect();
        let mut angle_sum = 0.0f64;
        let n_normals = angles.len();
        for i in 0..n_normals {
            let curr = angles[i];
            let next = angles[(i + 1) % n_normals];
            let mut diff = next - curr;
            while diff < -std::f64::consts::PI { diff += 2.0 * std::f64::consts::PI; }
            while diff >= std::f64::consts::PI { diff -= 2.0 * std::f64::consts::PI; }
            angle_sum += diff;
        }

        prop_assert!(
            (angle_sum - 2.0 * std::f64::consts::PI).abs() < 0.1 ||
            (angle_sum + 2.0 * std::f64::consts::PI).abs() < 0.1,
            "Normal angles should form one rotation. angle_sum={:.4}, angles={:?}",
            angle_sum, angles
        );
    }
}
