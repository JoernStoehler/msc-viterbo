# geom — Polytope Primitives and Shared Foundations

**Status:** Implementation complete

## Purpose

Shared geometric primitives for EHZ capacity algorithms. This crate provides:
- Polytope representation (H-rep)
- Volume computation via Qhull
- Systolic ratio calculation
- Numerical tolerances

All capacity algorithms (HK2017, Tube, Billiard) depend on this crate.

## Problem Statement

**Input:** A polytope K ⊂ ℝ⁴ with 0 ∈ int(K).

**Output:** The Ekeland-Hofer-Zehnder capacity c_EHZ(K) and a minimum-action closed Reeb orbit achieving it.

**The EHZ capacity:**
```
c_EHZ(K) = min { A(γ) : γ is a closed Reeb orbit on ∂K }
```

**Capacity axioms (what tests should verify):**
1. **Scaling:** c(λK) = λ² · c(K) for λ > 0
2. **Monotonicity:** K ⊆ L ⟹ c(K) ≤ c(L)
3. **Symplectic invariance:** c(AK + b) = c(K) for A ∈ Sp(4) and b ∈ ℝ⁴
4. **Normalization:** c(B⁴) = c(Z⁴) = π (ball and cylinder)

---

## Polytope Representation

### H-representation

A polytope is represented as the intersection of half-spaces:
```
K = ⋂ᵢ { x : ⟨nᵢ, x⟩ ≤ hᵢ }
```

```rust
pub struct PolytopeHRep {
    pub normals: Vec<Vector4<f64>>,  // unit outward normals
    pub heights: Vec<f64>,           // hᵢ > 0 (since 0 ∈ int(K))
}
```

**Code:** `polytope.rs`

**Validation:**
```rust
impl PolytopeHRep {
    pub fn validate(&self) -> Result<(), ValidationError> {
        // 1. Lengths match
        assert_eq!(normals.len(), heights.len());

        // 2. Normals are unit vectors
        assert!(normals.iter().all(|n| (n.norm() - 1.0).abs() < EPS_UNIT));

        // 3. Heights are positive (0 in interior)
        assert!(heights.iter().all(|&h| h > 0.0));

        // 4. At least 5 facets (minimum for 4D polytope)
        assert!(normals.len() >= 5);
    }
}
```

### Scaling

```rust
impl PolytopeHRep {
    /// Scale polytope by factor λ: K → λK
    /// Heights scale linearly: h'ᵢ = λ · hᵢ
    pub fn scale(&self, lambda: f64) -> Self {
        PolytopeHRep {
            normals: self.normals.clone(),
            heights: self.heights.iter().map(|h| h * lambda).collect(),
        }
    }
}
```

---

## Volume Computation

Compute 4D polytope volume using Qhull's Delaunay triangulation.

```rust
/// Compute volume of 4D polytope from H-representation.
///
/// Uses Qhull to convert H-rep → V-rep, then computes volume
/// via triangulation into 4-simplices.
pub fn polytope_volume_hrep(hrep: &PolytopeHRep) -> Result<f64, VolumeError>;
```

**Mathematical formula:** For a 4-simplex with vertices v₀, v₁, v₂, v₃, v₄:
```
Volume = (1/24) · |det([v₁-v₀, v₂-v₀, v₃-v₀, v₄-v₀])|
```

Total volume = sum over all simplices in triangulation.

**Code:** `volume.rs`

---

## Systolic Ratio

The systolic ratio measures how "efficient" a polytope is:
```
sys(K) = c_EHZ(K)² / (2 · Vol(K))
```

Viterbo's conjecture (disproven 2024): sys(K) ≤ 1 for all convex K.

```rust
/// Compute systolic ratio from capacity and volume.
///
/// # Panics
/// Panics if capacity or volume is non-positive.
pub fn systolic_ratio(capacity: f64, volume: f64) -> f64 {
    assert!(capacity > 0.0, "Capacity must be positive");
    assert!(volume > 0.0, "Volume must be positive");
    capacity * capacity / (2.0 * volume)
}
```

**Code:** `systolic.rs`

---

## Tolerances

```rust
/// General numerical tolerance for floating-point comparisons.
pub const EPS: f64 = 1e-10;

/// Tolerance for unit normal validation.
pub const EPS_UNIT: f64 = 1e-9;
```

**Code:** `tolerances.rs`

**Tolerance philosophy:**
- Tight tolerances for input validation (catch errors early)
- All tolerances are well above machine epsilon (~2.2e-16)
- Relative tolerance where possible: `|a - b| < EPS · max(|a|, |b|, 1.0)`

---

## Reeb Flow Fundamentals

These concepts are used by all capacity algorithms.

### Symplectic Form

The standard symplectic form on ℝ⁴:
```
ω(x, y) = ⟨Jx, y⟩ = q₁p₁' + q₂p₂' - p₁q₁' - p₂q₂'
```

where J is the standard complex structure:
```
J(q₁, q₂, p₁, p₂) = (-p₁, -p₂, q₁, q₂)
```

**Properties:**
- Antisymmetric: ω(x, y) = -ω(y, x)
- Non-degenerate: ω(x, y) = 0 for all y implies x = 0

### Reeb Vectors

The Reeb vector on facet Fᵢ with normal nᵢ and height hᵢ:
```
Rᵢ = (2/hᵢ) · J · nᵢ
```

**Properties:**
- Perpendicular to facet: ⟨Rᵢ, nᵢ⟩ = 0
- Magnitude: ‖Rᵢ‖ = 2/hᵢ

### Two-Faces and Adjacency

A **2-face** F_ij is the intersection of two facets:
```
F_ij = Fᵢ ∩ Fⱼ = K ∩ { x : ⟨nᵢ, x⟩ = hᵢ } ∩ { x : ⟨nⱼ, x⟩ = hⱼ }
```

Two facets are **adjacent** iff their 2-face is nonempty and 2-dimensional.

### Lagrangian vs Non-Lagrangian 2-Faces

A 2-face F_ij is **Lagrangian** iff ω(nᵢ, nⱼ) = 0.

**Significance:**
- Tube algorithm requires ALL 2-faces non-Lagrangian
- HK2017 works on all polytopes
- Billiard algorithm requires Lagrangian product structure

### Flow Direction

For a non-Lagrangian 2-face F_ij:
- If ω(nᵢ, nⱼ) > 0: Reeb flow crosses from Fᵢ to Fⱼ
- If ω(nᵢ, nⱼ) < 0: Reeb flow crosses from Fⱼ to Fᵢ

---

## Action Formula

For a closed piecewise-linear curve with vertices v₀, v₁, ..., vₙ = v₀:
```
A = (1/2) · Σₖ ω(vₖ, vₖ₊₁)
```

**For Reeb orbits:** Action equals period (T = Στₖ where τₖ are segment times).

---

## API

```rust
use geom::{PolytopeHRep, polytope_volume_hrep, systolic_ratio};

// Create polytope
let hrep = PolytopeHRep::new(normals, heights);
hrep.validate()?;

// Compute volume
let volume = polytope_volume_hrep(&hrep)?;

// After computing capacity with HK2017/Tube:
let sys = systolic_ratio(capacity, volume);
```

---

## Testing Strategy

| Test | Purpose | Location |
|------|---------|----------|
| Tesseract volume | Known value: 1.0 | `volume.rs:test_tesseract_volume` |
| Cross-polytope volume | Known value: 1/3 | `volume.rs:test_cross_polytope_volume` |
| Systolic ratio scaling | sys(λK) = sys(K) | `systolic.rs:test_systolic_ratio_scale_invariant` |
| Validation failures | Reject invalid input | `polytope.rs:test_*` |

---

## Dependencies

- `nalgebra`: Linear algebra (Vector4, Matrix4)
- `qhull`: Convex hull and Delaunay triangulation

---

## Related

- **HK2017 algorithm:** `packages/rust_viterbo/hk2017/`
- **Tube algorithm:** `packages/rust_viterbo/tube/`
- **Billiard algorithm:** `packages/rust_viterbo/billiard/`
