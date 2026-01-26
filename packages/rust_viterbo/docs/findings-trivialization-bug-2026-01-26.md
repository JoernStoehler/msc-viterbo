# Findings: Trivialization Bug Discovery Session (2026-01-26)

This document captures findings from an implementation attempt of the tube algorithm that revealed a fundamental error in developer-spec-v2.md.

## Executive Summary

The spec's trivialization formula `τ_n(V) = (⟨V, Jn⟩, ⟨V, Kn⟩)` does **not** provide a bijection on 2-face tangent spaces. This invalidates the round-trip property, breaks the transition matrix symplecticity claim, and cascades to affect rotation numbers, tube extension, and closure detection.

---

## 1. The Core Error

### 1.1 What the Spec Claims (§1.10)

The spec defines:
- **Trivialization**: `τ_n(V) = (⟨V, Jn⟩, ⟨V, Kn⟩)`
- **Inverse**: `τ_n⁻¹(a, b) = a·Jn + b·Kn`
- **Round-trip claim** (lines 546-550): `τ_n⁻¹ ∘ τ_n = identity` on tangent vectors

### 1.2 Why It's Wrong

**The image of τ_n⁻¹:**
```
Im(τ_n⁻¹) = span{Jn, Kn}
```
This is the 2D subspace perpendicular to `n` and `(JK)n`.

**The 2-face tangent space:**
```
T_{F_{ij}} = {V ∈ ℝ⁴ : ⟨V, n_i⟩ = 0 and ⟨V, n_j⟩ = 0}
```
This is the 2D subspace perpendicular to `n_i` and `n_j`.

**Key insight:** These are the **same** 2D subspace only when `n_j = ±(JK)n_i`. For generic 2-faces, they are different.

### 1.3 Concrete Counterexample

For the 4D cross-polytope with adjacent facet normals:
- `n₁ = (1, 1, 1, 1)/2`
- `n₂ = (1, 1, 1, -1)/2`

**2-face tangent space** (kernel of both normals):
```
T = span{(1, 0, -1, 0), (0, 1, -1, 0)}
```

**Trivialization image** span{Jn₁, Kn₁}:
```
Jn₁ = (-1, -1, 1, 1)/2
Kn₁ = (-1, 1, 1, -1)/2
```

**Verification:** The vector `v = (1, 0, -1, 0)` satisfies:
- `⟨v, n₁⟩ = (1 + 0 - 1 + 0)/2 = 0` ✓
- `⟨v, n₂⟩ = (1 + 0 - 1 - 0)/2 = 0` ✓

So `v ∈ T`. But `v ∉ span{Jn₁, Kn₁}`:
- Writing `v = a·Jn₁ + b·Kn₁` and solving yields no solution
- Alternatively: `⟨v, n₁⟩ = 0` but `⟨v, (JK)n₁⟩ ≠ 0`

Therefore `τ_{n₁}⁻¹ ∘ τ_{n₁}(v) ≠ v`.

---

## 2. Downstream Errors

### 2.1 Transition Matrix Not Symplectic (§1.11)

**Spec claim:** `det(ψ) = 1` where `ψ = τ_{n_j} ∘ τ_{n_i}⁻¹`

**Actual result:** For the cross-polytope example above, `det(ψ) = 0.5`

**Why:** The transition matrix is computed as:
```
ψ = [τ_{n₂}(Jn₁) | τ_{n₂}(Kn₁)]
```
This maps `span{Jn₁, Kn₁} → ℝ²`, which is a bijection from the **wrong** subspace. The symplectic form is not preserved because the domain isn't the 2-face tangent space.

### 2.2 Rotation Number Invalid (§1.12)

The rotation number formula:
```
ρ(F) = (1/2π) arccos(tr(ψ)/2)
```
assumes `ψ ∈ Sp(2)` (i.e., `det(ψ) = 1`). With `det(ψ) = 0.5`, the matrix isn't symplectic, so:
- The trace classification (elliptic/parabolic/hyperbolic) doesn't apply
- The rotation number has no geometric meaning

### 2.3 Tube Extension Broken (§5)

Tube extension uses the transition matrix to transform polygon vertices when crossing 2-faces. If `ψ` isn't symplectic:
- Areas aren't preserved
- The "symplectic width" interpretation fails
- Chord calculations are geometrically meaningless

### 2.4 Closure Detection Broken (§5.5)

Tube closure looks for the identity matrix (or scalar multiple) after composing transition matrices around a cycle. With non-symplectic matrices, the composition doesn't have the expected properties.

---

## 3. Places Where We Should Have Caught This Earlier

### 3.1 The Round-Trip Assertion (§1.10, lines 546-550)

The spec includes:
```rust
// Round-trip: untrivialize ∘ trivialize = identity on tangent vectors
// (only holds for vectors perpendicular to n)
let v_tangent = /* any vector with v.dot(n) == 0 */;
let v_recovered = untrivialize(n, &trivialize(n, &v_tangent));
assert!((v_recovered - v_tangent).norm() < EPS);
```

**Problem:** The comment says "perpendicular to n" but the 2-face tangent space requires perpendicularity to **both** n₁ and n₂. This assertion would pass for vectors in `span{Jn, Kn}` but fail for vectors in the actual 2-face tangent space.

**Should have:** The test should use a vector from the 2-face tangent space (perpendicular to both normals), not just any vector perpendicular to one normal.

### 3.2 The Symplectic Preservation Claim (§1.10, lines 553-577)

The spec claims `ω(V₁, V₂) = ω_std(τ_n(V₁), τ_n(V₂))` for vectors tangent to the facet.

**Problem:** This claim is only verified for vectors perpendicular to **one** normal. The actual use case (2-face tangent vectors) requires perpendicularity to **two** normals.

**Should have:** A test with two adjacent normals and vectors from their common tangent space.

### 3.3 Missing Concrete Cross-Polytope Test (§1.11)

The transition matrix section has no concrete numerical example. A simple test with cross-polytope normals would have immediately shown `det(ψ) ≠ 1`.

**Should add:**
```rust
#[test]
fn test_transition_matrix_cross_polytope() {
    let n1 = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
    let n2 = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();
    let psi = compute_transition_matrix(&n1, &n2);
    assert!((psi.determinant() - 1.0).abs() < 1e-10,
        "det(ψ) = {}, expected 1.0", psi.determinant());
}
```

### 3.4 The Note in §1.10 Was a Warning Sign

The spec says:
> **Note:** This function can be applied to any V ∈ ℝ⁴, but its geometric meaning requires V tangent to the facet (i.e., ⟨V, n⟩ = 0).

This hedging ("geometric meaning requires...") hints that the authors knew τ_n isn't a bijection on arbitrary subspaces. The note should have been a red flag that the 2-face tangent space (defined by **two** constraints) isn't the same as "tangent to one facet" (one constraint).

---

## 4. Additional Observations

### 4.1 Quaternion Naming Confusion (§1.9)

The spec uses `I = identity` in the quaternion matrices section:
```
I = identity, J = ..., K = ...
```

This conflicts with standard quaternion notation where `{1, i, j, k}` are the four basis elements and `i = jk`. The spec should either:
- Use `{1, J, K, M}` where `M = JK` (avoiding `I` for identity)
- Use `{Id, I, J, K}` with `I = JK` (standard quaternion naming)

The current notation `I = identity` is confusing because later we need the fourth quaternion matrix (which would naturally be called `I = JK`).

### 4.2 Reeb Flow Direction Implicit

The spec defines `J` and uses it for the symplectic form but doesn't explicitly state that the Reeb flow direction on a facet with normal `n` is `R = (2/h)·Jn`. This is mentioned in CH2021 and should be explicit in the spec since it's crucial for understanding why we trivialize "transverse to the flow."

### 4.3 Missing: What Should τ Actually Be?

The spec should clarify what CH2021 Definition 2.15 actually says. Possibilities:

1. **τ depends on both normals**: `τ_{n_i, n_j}: T_{F_{ij}} → ℝ²` using an orthonormal basis of the actual 2-face tangent space

2. **τ is a projection, not a bijection**: The current τ_n projects ℝ⁴ → ℝ² and the transition matrix formula needs adjustment to account for this

3. **Different parameterization**: CH2021 might use a different coordinate system entirely (e.g., via the Reeb flow parameterization)

---

## 5. Recommended Spec Fixes

### 5.1 Immediate (before any implementation)

1. **Read CH2021 Definition 2.15 carefully** and transcribe the exact trivialization formula with all notation defined

2. **Add concrete numerical tests** for cross-polytope in §1.10 and §1.11

3. **Fix the round-trip assertion** to test with actual 2-face tangent vectors

4. **Clarify quaternion naming** (§1.9)

### 5.2 Structural

1. **Separate "trivialization of one facet" from "trivialization of 2-face"** — these are different geometric objects

2. **Make the Reeb flow direction explicit** — add a section explaining `R = (2/h)Jn` and why we trivialize transverse to it

3. **Add a "verification" section** with numerical examples for each major formula

### 5.3 Tests to Add

```rust
// Test: 2-face tangent space vs trivialization image
#[test]
fn test_tangent_space_vs_trivialization_image() {
    // Cross-polytope normals
    let n1 = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
    let n2 = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

    // A vector in the 2-face tangent space
    let v = Vector4::new(1.0, 0.0, -1.0, 0.0);
    assert!(v.dot(&n1).abs() < EPS);
    assert!(v.dot(&n2).abs() < EPS);

    // Check if v is in span{Jn1, Kn1}
    let jn1 = J_MATRIX * n1;
    let kn1 = K_MATRIX * n1;

    // If v = a*jn1 + b*kn1, then v must satisfy:
    // v.dot(n1) = 0 (yes, by orthogonality of quaternion basis)
    // v.dot((J*K)*n1) = 0 (this is the second constraint for span{Jn1, Kn1})
    let m_n1 = J_MATRIX * K_MATRIX * n1;
    let v_dot_mn1 = v.dot(&m_n1);

    // This will FAIL if v is not in span{Jn1, Kn1}
    // Which demonstrates the bug
    assert!(v_dot_mn1.abs() < EPS,
        "v is in 2-face tangent space but NOT in span{{Jn1, Kn1}}: v·(JK)n1 = {}",
        v_dot_mn1);
}

// Test: transition matrix determinant
#[test]
fn test_transition_matrix_symplectic() {
    let n1 = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
    let n2 = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();
    let psi = compute_transition_matrix(&n1, &n2);

    assert!((psi.determinant() - 1.0).abs() < EPS,
        "Transition matrix not symplectic: det = {}", psi.determinant());
}
```

---

## 6. Summary

| Issue | Location | Severity | Status |
|-------|----------|----------|--------|
| Trivialization not bijective on 2-face tangent space | §1.10 | **Critical** | Needs fix |
| Transition matrix det ≠ 1 | §1.11 | Critical (downstream) | Blocked by above |
| Round-trip assertion tests wrong subspace | §1.10 | High | Needs fix |
| Quaternion naming confusing | §1.9 | Medium | Needs clarification |
| Reeb flow direction implicit | §1.9 | Medium | Should add |
| No concrete numerical tests | §1.10-§1.12 | High | Should add |

The tube algorithm implementation is blocked until the trivialization is correctly specified.
