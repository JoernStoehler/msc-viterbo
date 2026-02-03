//! 2D convex geometry primitives.
//!
//! This crate provides foundational types and operations for 2D convex geometry,
//! used by EHZ capacity algorithms when working with trivialized 2-face tangent spaces.
//!
//! # Types
//!
//! - [`Polygon`]: Convex polygon with vertices in counter-clockwise order
//!
//! # Functions
//!
//! - [`area`]: Compute polygon area (shoelace formula)
//!
//! # Design Principles
//!
//! 1. **Validated types**: [`Polygon::new`] validates all invariants; invalid input is rejected.
//! 2. **Documented proofs**: Each function has a correctness proof in its doc-comment.
//! 3. **Comprehensive tests**: Both positive (valid input accepted) and negative (invalid rejected) cases.
//!
//! # Example
//!
//! ```
//! use nalgebra::Vector2;
//! use geom2d::{Polygon, area};
//!
//! let triangle = Polygon::new(vec![
//!     Vector2::new(0.0, 0.0),
//!     Vector2::new(1.0, 0.0),
//!     Vector2::new(0.0, 1.0),
//! ]).expect("valid triangle");
//!
//! assert!((area(&triangle) - 0.5).abs() < 1e-10);
//! ```

pub mod area;
pub mod polygon;
pub mod tolerances;

pub use area::area;
pub use polygon::{Polygon, PolygonError};
pub use tolerances::{EPS, EPS_AREA, EPS_VERTEX, MAX_COORD};
