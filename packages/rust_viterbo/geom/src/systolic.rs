//! Systolic ratio computation for convex bodies in R⁴.
//!
//! The systolic ratio is a scale-invariant quantity defined as:
//!
//! ```text
//! sys(K) = c_EHZ(K)² / (2 · vol(K))
//! ```
//!
//! where:
//! - `c_EHZ(K)` is the Ekeland-Hofer-Zehnder capacity
//! - `vol(K)` is the 4-dimensional Lebesgue volume
//!
//! For balls and cylinders of radius r, sys(B(r)) = sys(Z(r)) = 1.
//!
//! # Reference
//!
//! See thesis chapter "Action, EHZ capacity, and systolic ratio" for mathematical details.

/// Compute the systolic ratio from capacity and volume.
///
/// # Formula
///
/// ```text
/// sys(K) = c² / (2 · vol)
/// ```
///
/// # Arguments
///
/// - `capacity`: The EHZ capacity c_EHZ(K) (must be > 0)
/// - `volume`: The 4D volume (must be > 0)
///
/// # Returns
///
/// The systolic ratio, a dimensionless positive number.
///
/// # Panics
///
/// Panics if `capacity` or `volume` is non-positive or NaN.
///
/// # Example
///
/// ```
/// use geom::systolic::systolic_ratio;
///
/// // Ball of radius 2: capacity = 4π, volume = π²·2⁴/2
/// // For verification, use a simpler example:
/// // If capacity = 4.0 and volume = 16.0, then sys = 16/(2·16) = 0.5
/// let sys = systolic_ratio(4.0, 16.0);
/// assert!((sys - 0.5).abs() < 1e-10);
/// ```
pub fn systolic_ratio(capacity: f64, volume: f64) -> f64 {
    assert!(
        capacity > 0.0 && capacity.is_finite(),
        "capacity must be positive and finite, got {capacity}"
    );
    assert!(
        volume > 0.0 && volume.is_finite(),
        "volume must be positive and finite, got {volume}"
    );

    capacity * capacity / (2.0 * volume)
}

#[cfg(test)]
mod tests {
    use super::*;

    const TOL: f64 = 1e-10;

    #[test]
    fn test_systolic_ratio_basic() {
        // capacity = 4.0, volume = 16.0
        // sys = 16 / 32 = 0.5
        let sys = systolic_ratio(4.0, 16.0);
        assert!((sys - 0.5).abs() < TOL);
    }

    #[test]
    fn test_systolic_ratio_ball() {
        // For a ball of radius r: c = 2πr, vol = (π²/2)r⁴
        // sys = (2πr)² / (2 · π²r⁴/2) = 4π²r² / (π²r⁴) = 4/r²
        // Wait, that doesn't give sys = 1. Let me recalculate.

        // Actually, for 4D ball B⁴(r):
        // - Volume = (π²/2) r⁴
        // - Capacity c_EHZ(B⁴(r)) = πr²
        // - sys = (πr²)² / (2 · π²r⁴/2) = π²r⁴ / (π²r⁴) = 1 ✓

        let r = 2.0;
        let capacity = std::f64::consts::PI * r * r;
        let volume = std::f64::consts::PI * std::f64::consts::PI * r.powi(4) / 2.0;
        let sys = systolic_ratio(capacity, volume);

        assert!(
            (sys - 1.0).abs() < TOL,
            "ball systolic ratio should be 1, got {sys}"
        );
    }

    #[test]
    fn test_systolic_ratio_cylinder() {
        // For a cylinder Z(r) = B²(r) × ℝ²:
        // - Volume = πr² · (height of disk in ℝ²) -- but this is infinite for actual cylinder
        // - For bounded cylinder Z(r,h) = B²(r) × [-h/2, h/2]²:
        //   Volume = πr² · h²
        //   Capacity = πr² (independent of h)
        //   sys = (πr²)² / (2 · πr² · h²) = πr² / (2h²)
        //
        // For sys = 1, need h² = πr²/2, i.e., h = r√(π/2)

        // Let's verify with r=1, h=√(π/2)
        let r = 1.0;
        let h = (std::f64::consts::PI / 2.0).sqrt();
        let capacity = std::f64::consts::PI * r * r;
        let volume = std::f64::consts::PI * r * r * h * h;
        let sys = systolic_ratio(capacity, volume);

        assert!(
            (sys - 1.0).abs() < TOL,
            "cylinder systolic ratio should be 1 for h=r√(π/2), got {sys}"
        );
    }

    #[test]
    fn test_systolic_ratio_scale_invariant() {
        // Scaling K by λ multiplies capacity by λ² and volume by λ⁴
        // sys(λK) = (λ²c)² / (2·λ⁴·vol) = λ⁴c² / (2λ⁴·vol) = c²/(2·vol) = sys(K)

        let c1 = 4.0;
        let v1 = 16.0;
        let sys1 = systolic_ratio(c1, v1);

        let lambda = 3.0;
        let c2 = lambda * lambda * c1;
        let v2 = lambda.powi(4) * v1;
        let sys2 = systolic_ratio(c2, v2);

        assert!(
            (sys1 - sys2).abs() < TOL,
            "systolic ratio should be scale-invariant"
        );
    }

    #[test]
    #[should_panic(expected = "capacity must be positive")]
    fn test_systolic_ratio_negative_capacity() {
        systolic_ratio(-1.0, 16.0);
    }

    #[test]
    #[should_panic(expected = "volume must be positive")]
    fn test_systolic_ratio_negative_volume() {
        systolic_ratio(4.0, -16.0);
    }

    #[test]
    #[should_panic(expected = "capacity must be positive")]
    fn test_systolic_ratio_zero_capacity() {
        systolic_ratio(0.0, 16.0);
    }

    #[test]
    #[should_panic(expected = "volume must be positive")]
    fn test_systolic_ratio_zero_volume() {
        systolic_ratio(4.0, 0.0);
    }

    /// S2: Scale invariance holds at extreme scale factors (λ = 1e-8, 1e8)
    #[test]
    fn test_scale_invariance_extreme() {
        let c_base = 4.0;
        let v_base = 16.0;
        let sys_base = systolic_ratio(c_base, v_base);

        // Test with extreme scaling factors
        for &lambda in &[1e-8, 1e8] {
            // Scaling K by λ: capacity scales as λ², volume scales as λ⁴
            let c_scaled = lambda * lambda * c_base;
            let v_scaled = lambda.powi(4) * v_base;
            let sys_scaled = systolic_ratio(c_scaled, v_scaled);

            // Relative error should be small even at extreme scales
            let rel_error = (sys_scaled - sys_base).abs() / sys_base;
            assert!(
                rel_error < 1e-10,
                "Scale invariance failed at λ={}: sys_base={}, sys_scaled={}, rel_error={}",
                lambda,
                sys_base,
                sys_scaled,
                rel_error
            );
        }
    }
}
