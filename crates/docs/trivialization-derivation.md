# Trivialization Derivation: Two Approaches

**Date:** 2026-01-26
**Purpose:** Correct derivation of 2-face trivialization, fixing the bug identified in `findings-trivialization-bug-2026-01-26.md`.

---

## 0. Quaternion Matrices (from CH2021)

CH2021 uses quaternion matrices **i**, **j**, **k** ∈ SO(4) satisfying:
- i² = j² = k² = -I
- ij = k, jk = i, ki = j
- **i** is the standard almost complex structure

Explicit matrices (in coordinates x₁, x₂, y₁, y₂):

```
        ⎡ 0  0 -1  0 ⎤         ⎡ 0 -1  0  0 ⎤         ⎡ 0  0  0 -1 ⎤
quat_i = ⎢ 0  0  0 -1 ⎥  quat_j = ⎢ 1  0  0  0 ⎥  quat_k = ⎢ 0  0  1  0 ⎥
        ⎢ 1  0  0  0 ⎥         ⎢ 0  0  0  1 ⎥         ⎢ 0 -1  0  0 ⎥
        ⎣ 0  1  0  0 ⎦         ⎣ 0  0 -1  0 ⎦         ⎣ 1  0  0  0 ⎦
```

**Key properties:**
- ω₀(u, v) = ⟨quat_i · u, v⟩ (symplectic form)
- ω₀(quat_j · ν, quat_k · ν) = 1 for any unit vector ν
- {quat_i · ν, quat_j · ν, quat_k · ν} is orthonormal for any unit ν

---

## 1. Geometric Setup

### 1.1 The 2-Face

A **2-face** F is the intersection of two 3-faces (facets):
- F = F_entry ∩ F_exit
- n_entry = outward unit normal to entry facet
- n_exit = outward unit normal to exit facet

The **tangent space** TF is 2-dimensional:
```
TF = {V ∈ ℝ⁴ : ⟨V, n_entry⟩ = 0 and ⟨V, n_exit⟩ = 0}
```

### 1.2 Flow Direction

The Reeb vector on a facet with normal ν is R = (2/h) · quat_i · ν.

For a non-Lagrangian 2-face, the flow crosses from one facet to the other. The direction is determined by:
```
⟨quat_i · n_entry, n_exit⟩ > 0  ⟹  flow goes entry → exit
⟨quat_i · n_entry, n_exit⟩ < 0  ⟹  flow goes exit → entry
```

We assume the 2-face is oriented so that flow goes entry → exit.

---

## 2. CH2021 Trivialization (Definition 2.15)

### 2.1 The Map τ_F

CH2021 defines:
```
τ_F: TF → ℝ²
τ_F(V) = (⟨V, quat_j · ν⟩, ⟨V, quat_k · ν⟩)
```
where ν = n_exit (the EXIT facet's normal).

**Why this works:**
- {quat_i · ν, quat_j · ν, quat_k · ν} is an orthonormal basis for T(F_exit)
- TF ⊂ T(F_exit) (2-face tangent space is inside 3-face tangent space)
- Any V ∈ TF can be written V = a · quat_i · ν + b · quat_j · ν + c · quat_k · ν
- τ_F(V) = (b, c) extracts the (quat_j, quat_k) components

**Symplectic preservation:** ω₀(quat_j · ν, quat_k · ν) = 1, so τ_F preserves the symplectic form.

### 2.2 The Alternate Convention τ'_F

Using the ENTRY normal ν' = n_entry:
```
τ'_F: TF → ℝ²
τ'_F(V) = (⟨V, quat_j · ν'⟩, ⟨V, quat_k · ν'⟩)
```

### 2.3 Transition Matrix ψ_F

The transition matrix converts entry coordinates to exit coordinates:
```
ψ_F = τ_F ∘ (τ'_F)⁻¹ ∈ Sp(2)
```

**CH2021 explicit formula** (Lemma 2.17):

Let:
```
a₁ = ⟨ν', ν⟩ = ⟨n_entry, n_exit⟩
a₂ = ⟨quat_i · ν', ν⟩ = ⟨quat_i · n_entry, n_exit⟩
a₃ = ⟨quat_j · ν', ν⟩ = ⟨quat_j · n_entry, n_exit⟩
a₄ = ⟨quat_k · ν', ν⟩ = ⟨quat_k · n_entry, n_exit⟩
```

Then:
```
        1   ⎡ a₁a₂ - a₃a₄    -(a₂² + a₄²) ⎤
ψ_F = ─── · ⎢                              ⎥
       a₂   ⎣  a₂² + a₃²      a₁a₂ + a₃a₄  ⎦
```

**Properties:**
- det(ψ_F) = 1 (symplectic)
- tr(ψ_F) = 2a₁ = 2⟨n_entry, n_exit⟩ ∈ (-2, 2) for non-Lagrangian 2-faces
- a₂ > 0 (by flow direction convention)
- ψ_F is positive elliptic

---

## 3. Explicit Basis Approach (Option B)

### 3.1 Goal

Find basis vectors b₁, b₂ ∈ TF such that:
- τ_F(b₁) = (1, 0)
- τ_F(b₂) = (0, 1)

Then reconstruction is trivial: for coords (a, b), the 4D point is:
```
point_4d = centroid + a · b₁ + b · b₂
```

### 3.2 Derivation

**Exit basis** (gives coordinates compatible with τ_F using n_exit):

bExit₁ must satisfy:
```
⟨bExit₁, n_entry⟩ = 0       (in TF)
⟨bExit₁, n_exit⟩ = 0        (in TF)
⟨bExit₁, quat_j · n_exit⟩ = 1   (first coord = 1)
⟨bExit₁, quat_k · n_exit⟩ = 0   (second coord = 0)
```

This is 4 linear equations in 4 unknowns. Define matrix M_exit with rows:
```
M_exit = ⎡ n_entry        ⎤
         ⎢ n_exit         ⎥
         ⎢ quat_j · n_exit ⎥
         ⎣ quat_k · n_exit ⎦
```

Then:
```
bExit₁ = 3rd column of M_exit⁻¹
bExit₂ = 4th column of M_exit⁻¹
```

**Entry basis** (gives coordinates compatible with τ'_F using n_entry):

Define M_entry with rows:
```
M_entry = ⎡ n_entry         ⎤
          ⎢ n_exit          ⎥
          ⎢ quat_j · n_entry ⎥
          ⎣ quat_k · n_entry ⎦
```

Then:
```
bEntry₁ = 3rd column of M_entry⁻¹
bEntry₂ = 4th column of M_entry⁻¹
```

### 3.3 Transition Matrix from Bases

The transition matrix ψ converts entry coords to exit coords.

Since τ'_F⁻¹(1, 0) = bEntry₁ and τ'_F⁻¹(0, 1) = bEntry₂:
```
ψ · [1, 0]ᵀ = τ_F(bEntry₁) = (⟨bEntry₁, quat_j · n_exit⟩, ⟨bEntry₁, quat_k · n_exit⟩)
ψ · [0, 1]ᵀ = τ_F(bEntry₂) = (⟨bEntry₂, quat_j · n_exit⟩, ⟨bEntry₂, quat_k · n_exit⟩)
```

Therefore:
```
    ⎡ ⟨bEntry₁, quat_j · n_exit⟩   ⟨bEntry₂, quat_j · n_exit⟩ ⎤
ψ = ⎢                                                          ⎥
    ⎣ ⟨bEntry₁, quat_k · n_exit⟩   ⟨bEntry₂, quat_k · n_exit⟩ ⎦
```

---

## 4. Rotation Number

For a symplectic 2×2 matrix ψ with |tr(ψ)| < 2 (elliptic case):

```
ρ = (1/2π) · arccos(tr(ψ)/2)
```

For our transition matrix:
```
tr(ψ_F) = 2⟨n_entry, n_exit⟩
ρ(F) = (1/2π) · arccos(⟨n_entry, n_exit⟩)
```

**Range:** Since ⟨n_entry, n_exit⟩ ∈ (-1, 1) for non-Lagrangian 2-faces, we have ρ ∈ (0, 1/2).

---

## 5. Verification Tests

### 5.1 Cross-Polytope Test (The Bug-Exposing Case)

```rust
#[test]
fn test_cross_polytope_trivialization() {
    let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
    let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

    // Option A: CH2021 direct formula
    let psi_direct = compute_psi_ch2021_direct(&n_entry, &n_exit);

    // Option B: Explicit basis approach
    let (b_entry, b_exit) = compute_basis_vectors(&n_entry, &n_exit);
    let psi_basis = compute_psi_from_bases(&b_entry, &n_exit);

    // Both should match
    assert!((psi_direct - psi_basis).norm() < 1e-10,
        "Direct and basis approaches disagree");

    // Both should be symplectic
    assert!((psi_direct.determinant() - 1.0).abs() < 1e-10,
        "Direct formula not symplectic: det = {}", psi_direct.determinant());
    assert!((psi_basis.determinant() - 1.0).abs() < 1e-10,
        "Basis formula not symplectic: det = {}", psi_basis.determinant());

    // Trace should be 2⟨n_entry, n_exit⟩
    let expected_trace = 2.0 * n_entry.dot(&n_exit);
    assert!((psi_direct.trace() - expected_trace).abs() < 1e-10,
        "Trace mismatch: got {}, expected {}", psi_direct.trace(), expected_trace);
}
```

### 5.2 Basis Vector Validity

```rust
#[test]
fn test_basis_vectors_in_tangent_space() {
    let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
    let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

    let (b_entry, b_exit) = compute_basis_vectors(&n_entry, &n_exit);

    // All basis vectors should be perpendicular to BOTH normals
    for b in &b_exit {
        assert!(b.dot(&n_entry).abs() < 1e-10, "bExit not perp to n_entry");
        assert!(b.dot(&n_exit).abs() < 1e-10, "bExit not perp to n_exit");
    }
    for b in &b_entry {
        assert!(b.dot(&n_entry).abs() < 1e-10, "bEntry not perp to n_entry");
        assert!(b.dot(&n_exit).abs() < 1e-10, "bEntry not perp to n_exit");
    }

    // Exit basis should give identity under τ_F
    let qj_exit = QUAT_J * n_exit;
    let qk_exit = QUAT_K * n_exit;
    assert!((b_exit[0].dot(&qj_exit) - 1.0).abs() < 1e-10);
    assert!(b_exit[0].dot(&qk_exit).abs() < 1e-10);
    assert!(b_exit[1].dot(&qj_exit).abs() < 1e-10);
    assert!((b_exit[1].dot(&qk_exit) - 1.0).abs() < 1e-10);
}
```

### 5.3 Round-Trip Test

```rust
#[test]
fn test_reconstruction_round_trip() {
    let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
    let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

    let (_, b_exit) = compute_basis_vectors(&n_entry, &n_exit);
    let centroid = Vector4::new(0.5, 0.5, 0.5, 0.0);  // example

    // Create a point in TF
    let coords = Vector2::new(0.3, 0.7);
    let point_4d = centroid + coords[0] * b_exit[0] + coords[1] * b_exit[1];

    // Verify it's in TF
    assert!((point_4d - centroid).dot(&n_entry).abs() < 1e-10);
    assert!((point_4d - centroid).dot(&n_exit).abs() < 1e-10);

    // Trivialize and check we get back the same coords
    let qj_exit = QUAT_J * n_exit;
    let qk_exit = QUAT_K * n_exit;
    let recovered = Vector2::new(
        (point_4d - centroid).dot(&qj_exit),
        (point_4d - centroid).dot(&qk_exit),
    );
    assert!((recovered - coords).norm() < 1e-10);
}
```

---

## 6. What the Old Spec Got Wrong

The old spec (developer-spec-v2.md §1.10) claimed:
```
τ_n⁻¹(a, b) = a · quat_j · n + b · quat_k · n   // WRONG
```

This gives a vector in span{quat_j · n, quat_k · n}, which is NOT the same as TF.

The correct inverse requires finding the unique V ∈ TF satisfying the coordinate equations, which is what our explicit basis approach does.

---

## 7. Summary

| Aspect | Old Spec (Wrong) | Option A (CH2021 Direct) | Option B (Explicit Basis) |
|--------|------------------|--------------------------|---------------------------|
| Inverse formula | a·Jn + b·Kn | Complex projection | V = a·b₁ + b·b₂ |
| Domain of inverse | span{Jn, Kn} | TF | TF |
| Reconstruction | Broken | Requires complex formula | Trivial |
| Transition matrix | det ≠ 1 | det = 1 (proven) | det = 1 (by construction) |

Both Option A and Option B are correct. Option B is preferable for implementation because reconstruction is trivial.
