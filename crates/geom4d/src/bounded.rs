//! Boundedness check for polytopes via linear programming.
//!
//! # Mathematical Background
//!
//! An H-representation K = ⋂ᵢ {x : ⟨nᵢ, x⟩ ≤ hᵢ} is **bounded** if and only if
//! the normals {n₁, ..., nₖ} **positively span** ℝ⁴.
//!
//! ## Definition: Positive Span
//!
//! A set of vectors S positively spans ℝⁿ iff for every direction d ∈ ℝⁿ \ {0},
//! there exists some v ∈ S with ⟨v, d⟩ > 0.
//!
//! Equivalently: there is no direction d ≠ 0 with ⟨v, d⟩ ≤ 0 for all v ∈ S.
//!
//! ## Why Positive Span ⟺ Bounded
//!
//! **Claim:** K is bounded ⟺ normals positively span ℝ⁴.
//!
//! **Proof:**
//!
//! (⟸) Suppose normals positively span ℝ⁴. For any direction d, some normal nᵢ
//! has ⟨nᵢ, d⟩ > 0. Moving in direction d eventually violates ⟨nᵢ, x⟩ ≤ hᵢ.
//! So K is bounded in every direction.
//!
//! (⟹) Suppose normals do NOT positively span ℝ⁴. Then there exists d ≠ 0 with
//! ⟨nᵢ, d⟩ ≤ 0 for all i. For any x ∈ K and t ≥ 0:
//! ⟨nᵢ, x + td⟩ = ⟨nᵢ, x⟩ + t⟨nᵢ, d⟩ ≤ hᵢ + 0 = hᵢ.
//! So x + td ∈ K for all t ≥ 0, meaning K is unbounded in direction d. □
//!
//! # Algorithm
//!
//! We check if there exists a recession direction d ≠ 0 with ⟨nᵢ, d⟩ ≤ 0 for all i.
//!
//! Since d ≠ 0 cannot be directly encoded in an LP, we check 8 LPs, one for each
//! normalization d[j] = ±1 (j = 0..4). If any LP is feasible, a recession direction
//! exists and the polytope is unbounded.
//!
//! This is complete because if d ≠ 0 is a recession direction, some component d[j] ≠ 0,
//! and we can scale d so that d[j] = ±1.
//!
//! # References
//!
//! - Positive span: Rockafellar, "Convex Analysis", Section 2.
//! - Recession cones: Rockafellar, "Convex Analysis", Section 8.

use minilp::{ComparisonOp, OptimizationDirection, Problem};
use nalgebra::Vector4;

use crate::tolerances::EPS_UNIT;

/// Check if a set of normals positively spans ℝ⁴ (polytope is bounded).
///
/// # Mathematical Statement
///
/// Returns `true` iff the normals {n₁, ..., nₖ} positively span ℝ⁴, i.e.,
/// for every d ∈ ℝ⁴ \ {0}, some nᵢ has ⟨nᵢ, d⟩ > 0.
///
/// # Proof of Correctness
///
/// **Claim:** `is_bounded(normals)` returns `true` iff normals positively span ℝ⁴.
///
/// **Proof:**
///
/// We check 8 LPs, testing if there exists d with ⟨nᵢ, d⟩ ≤ 0 for all i and d[j] = ±1.
///
/// (⟹) If any LP is feasible with solution d, then d ≠ 0 and ⟨nᵢ, d⟩ ≤ 0 for all i.
/// So d is a recession direction, normals don't positively span, return false.
///
/// (⟸) If normals don't positively span, there exists d ≠ 0 with ⟨nᵢ, d⟩ ≤ 0 for all i.
/// Since d ≠ 0, some component d[j] ≠ 0. Scale d so that d[j] = ±1 (preserving the
/// sign of ⟨nᵢ, d⟩). This scaled d is feasible for one of the 8 LPs.
///
/// Therefore: some LP feasible ⟺ unbounded, all LPs infeasible ⟺ bounded. □
///
/// # Preconditions
///
/// - `normals.len() >= 5` (minimum for 4D polytope with interior)
/// - All normals are unit vectors (‖nᵢ‖ = 1)
///
/// These are checked via `debug_assert!` in debug builds.
///
/// # Example
///
/// ```
/// use nalgebra::Vector4;
/// use geom4d::is_bounded;
///
/// // Tesseract normals: ±e₁, ±e₂, ±e₃, ±e₄
/// let tesseract_normals = vec![
///     Vector4::new(1.0, 0.0, 0.0, 0.0),
///     Vector4::new(-1.0, 0.0, 0.0, 0.0),
///     Vector4::new(0.0, 1.0, 0.0, 0.0),
///     Vector4::new(0.0, -1.0, 0.0, 0.0),
///     Vector4::new(0.0, 0.0, 1.0, 0.0),
///     Vector4::new(0.0, 0.0, -1.0, 0.0),
///     Vector4::new(0.0, 0.0, 0.0, 1.0),
///     Vector4::new(0.0, 0.0, 0.0, -1.0),
/// ];
///
/// assert!(is_bounded(&tesseract_normals));
/// ```
#[must_use]
pub fn is_bounded(normals: &[Vector4<f64>]) -> bool {
    // Precondition: at least 5 normals
    debug_assert!(
        normals.len() >= 5,
        "is_bounded: need at least 5 normals for a 4D polytope, got {}",
        normals.len()
    );

    // Precondition: all normals are unit vectors
    debug_assert!(
        normals.iter().all(|n| (n.norm() - 1.0).abs() < EPS_UNIT),
        "is_bounded: all normals must be unit vectors"
    );

    // Check if there exists a recession direction d ≠ 0 with ⟨nᵢ, d⟩ ≤ 0 for all i.
    //
    // We check 8 LPs, one for each normalization dⱼ = ±1. If any is feasible,
    // a recession direction exists and the polytope is unbounded.
    //
    // This covers all cases because if d ≠ 0, some component is nonzero and
    // can be scaled to ±1.

    for j in 0..4 {
        for &sign in &[-1.0, 1.0] {
            if has_recession_direction_with_normalization(normals, j, sign) {
                return false; // Unbounded
            }
        }
    }

    true // Bounded
}

/// Check if there exists d with ⟨nᵢ, d⟩ ≤ 0 for all i and d[axis] = sign.
fn has_recession_direction_with_normalization(
    normals: &[Vector4<f64>],
    axis: usize,
    sign: f64,
) -> bool {
    let mut problem = Problem::new(OptimizationDirection::Minimize);

    // Variables: d[0], d[1], d[2], d[3]
    let bound = 1e10;
    let d: Vec<_> = (0..4)
        .map(|k| {
            if k == axis {
                // Fix d[axis] = sign
                problem.add_var(0.0, (sign, sign))
            } else {
                problem.add_var(0.0, (-bound, bound))
            }
        })
        .collect();

    // Constraints: ⟨nᵢ, d⟩ ≤ 0 for all i
    for n in normals {
        problem.add_constraint(
            [(d[0], n[0]), (d[1], n[1]), (d[2], n[2]), (d[3], n[3])],
            ComparisonOp::Le,
            0.0,
        );
    }

    // Feasible → recession direction exists
    problem.solve().is_ok()
}

#[cfg(test)]
#[path = "bounded_tests.rs"]
mod tests;
