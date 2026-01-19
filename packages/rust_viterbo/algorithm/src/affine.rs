//! 2D affine algebra for tube flow map composition.
//!
//! The tube algorithm reduces 4D flow maps to 2D affine maps via trivialization.
//! This module provides the algebraic foundation for composing these maps and
//! finding fixed points (which correspond to closed Reeb orbits).
//!
//! See thesis §4.3 for the mathematical background on why 2D affine algebra suffices.

use rust_viterbo_geom::{Matrix2f, Vector2f};

/// A 2D affine map: f(x) = Ax + b
///
/// Used to represent the 2D projection of flow maps between facets.
/// Composition of tubes corresponds to composition of these affine maps.
#[derive(Clone, Debug)]
pub struct AffineMap2D {
    pub linear: Matrix2f,
    pub offset: Vector2f,
}

impl AffineMap2D {
    pub fn new(linear: Matrix2f, offset: Vector2f) -> Self {
        Self { linear, offset }
    }

    pub fn identity() -> Self {
        Self {
            linear: Matrix2f::identity(),
            offset: Vector2f::zeros(),
        }
    }

    /// Apply the map: f(x) = Ax + b
    pub fn apply(&self, x: Vector2f) -> Vector2f {
        self.linear * x + self.offset
    }

    /// Compose: (self ∘ other)(x) = self(other(x)) = A1(A2*x + b2) + b1
    pub fn compose(&self, other: &AffineMap2D) -> AffineMap2D {
        AffineMap2D {
            linear: self.linear * other.linear,
            offset: self.linear * other.offset + self.offset,
        }
    }

    /// Find the fixed point of the affine map, if it exists and is unique.
    /// Fixed point: x = Ax + b => (I - A)x = b
    ///
    /// A fixed point corresponds to a closed Reeb orbit starting point.
    pub fn fixed_point(&self) -> Option<Vector2f> {
        let i_minus_a = Matrix2f::identity() - self.linear;
        let lu = i_minus_a.lu();
        lu.solve(&self.offset)
    }
}

/// A 2D affine function: f(x) = g·x + c
///
/// Used to track accumulated action along a tube composition.
/// The action is affine in the starting point coordinates.
#[derive(Clone, Debug)]
pub struct AffineFunc {
    pub gradient: Vector2f,
    pub constant: f64,
}

impl AffineFunc {
    pub fn new(gradient: Vector2f, constant: f64) -> Self {
        Self { gradient, constant }
    }

    pub fn zero() -> Self {
        Self {
            gradient: Vector2f::zeros(),
            constant: 0.0,
        }
    }

    /// Evaluate: f(x) = g·x + c
    pub fn eval(&self, x: Vector2f) -> f64 {
        self.gradient.dot(&x) + self.constant
    }

    /// Compose with affine map: (f ∘ φ)(x) = f(φ(x)) = g·(Ax + b) + c
    pub fn compose(&self, map: &AffineMap2D) -> AffineFunc {
        AffineFunc {
            gradient: map.linear.transpose() * self.gradient,
            constant: self.gradient.dot(&map.offset) + self.constant,
        }
    }

    /// Add two affine functions: (f + g)(x) = f(x) + g(x)
    pub fn add(&self, other: &AffineFunc) -> AffineFunc {
        AffineFunc {
            gradient: self.gradient + other.gradient,
            constant: self.constant + other.constant,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identity_apply() {
        let id = AffineMap2D::identity();
        let v = Vector2f::new(1.0, 2.0);
        let result = id.apply(v);
        assert!((result - v).norm() < 1e-12);
    }

    #[test]
    fn compose_with_identity() {
        let m = AffineMap2D::new(
            Matrix2f::new(1.0, 2.0, 3.0, 4.0),
            Vector2f::new(5.0, 6.0),
        );
        let id = AffineMap2D::identity();
        let composed = m.compose(&id);
        let v = Vector2f::new(1.0, 2.0);
        assert!((composed.apply(v) - m.apply(v)).norm() < 1e-12);
    }

    #[test]
    fn compose_associative() {
        let a = AffineMap2D::new(Matrix2f::new(1.0, 2.0, 0.0, 1.0), Vector2f::new(1.0, 0.0));
        let b = AffineMap2D::new(Matrix2f::new(2.0, 0.0, 1.0, 2.0), Vector2f::new(0.0, 1.0));
        let c = AffineMap2D::new(Matrix2f::new(1.0, 1.0, -1.0, 1.0), Vector2f::new(-1.0, 1.0));
        let v = Vector2f::new(3.0, -2.0);
        let ab_c = a.compose(&b).compose(&c);
        let a_bc = a.compose(&b.compose(&c));
        assert!((ab_c.apply(v) - a_bc.apply(v)).norm() < 1e-12);
    }

    #[test]
    fn fixed_point_exists() {
        // Map: x → 0.5*x + (1, 1) has fixed point at (2, 2)
        let m = AffineMap2D::new(Matrix2f::new(0.5, 0.0, 0.0, 0.5), Vector2f::new(1.0, 1.0));
        let fp = m.fixed_point().unwrap();
        assert!((fp - Vector2f::new(2.0, 2.0)).norm() < 1e-12);
    }

    #[test]
    fn fixed_point_identity() {
        // Identity map has no unique fixed point (all points are fixed)
        let id = AffineMap2D::identity();
        assert!(id.fixed_point().is_none());
    }

    #[test]
    fn func_eval_zero() {
        let f = AffineFunc::zero();
        let v = Vector2f::new(1.0, 2.0);
        assert!((f.eval(v)).abs() < 1e-12);
    }

    #[test]
    fn func_eval_linear() {
        let f = AffineFunc::new(Vector2f::new(1.0, 2.0), 3.0);
        let v = Vector2f::new(1.0, 1.0);
        assert!((f.eval(v) - 6.0).abs() < 1e-12); // 1*1 + 2*1 + 3 = 6
    }

    #[test]
    fn func_compose_with_map() {
        let f = AffineFunc::new(Vector2f::new(1.0, 0.0), 0.0); // f(x) = x₁
        let m = AffineMap2D::new(Matrix2f::new(2.0, 0.0, 0.0, 1.0), Vector2f::new(1.0, 0.0));
        let composed = f.compose(&m);
        let v = Vector2f::new(1.0, 1.0);
        // f(m(v)) = f(2*1+1, 1) = f(3, 1) = 3
        assert!((composed.eval(v) - 3.0).abs() < 1e-12);
    }

    #[test]
    fn func_add() {
        let f = AffineFunc::new(Vector2f::new(1.0, 0.0), 1.0);
        let g = AffineFunc::new(Vector2f::new(0.0, 2.0), 2.0);
        let sum = f.add(&g);
        let v = Vector2f::new(1.0, 1.0);
        assert!((sum.eval(v) - 6.0).abs() < 1e-12); // 1 + 2 + 1 + 2 = 6
    }
}
