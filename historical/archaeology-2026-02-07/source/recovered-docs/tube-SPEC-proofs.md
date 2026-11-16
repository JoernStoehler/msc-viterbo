# tube — Proofs and Derivations

Detailed derivations supporting [SPEC.md](SPEC.md). Agents should read SPEC.md first; consult this file when verifying correctness.

---

## Why Action is Affine in Starting Position

**Claim:** For a tube with fixed facet sequence, the action of any trajectory is an affine function of its starting point in trivialized coordinates.

**Derivation:**

1. **Reeb flow is linear:** On facet with normal n, the flow is p(t) = p₀ + t · Rₙ where Rₙ is the Reeb vector.

2. **Exit time is affine in starting position:** To exit facet n and enter facet n', solve ⟨n', p(t)⟩ = h':
   ```
   t_exit = (h' - ⟨n', p₀⟩) / ⟨n', Rₙ⟩
   ```
   This is affine in p₀ (the denominator is constant for a given facet pair).

3. **Segment action = segment time:** For Reeb flow, A(γ) = T (action equals period). Each segment contributes t_exit - t_entry.

4. **Composition preserves affinity:** The exit point p(t_exit) is affine in p₀. By induction, all breakpoints are affine in the initial starting position.

5. **Sum of affine functions is affine:** Total action = Σₖ tₖ(p₀) where each tₖ is affine in p₀.

Therefore `action_func` is representable as f(x) = ⟨g, x⟩ + c for some gradient g and constant c.

---

## Action Lower Bound for Branch-and-Bound

**Claim:** The minimum action over a tube equals the minimum of `action_func` evaluated at the vertices of `p_start`.

**Derivation:**

The action function is affine: action(s) = ⟨g, s⟩ + c.

For a convex polygon P, the minimum of an affine function over P occurs at a vertex:
- Affine functions are both convex and concave
- On a convex set, the minimum of a convex function occurs at an extreme point
- Vertices are the extreme points of a convex polygon

Therefore:
```rust
fn action_lower_bound(&self) -> f64 {
    self.p_start.vertices.iter()
        .map(|v| self.action_func.gradient.dot(v) + self.action_func.constant)
        .fold(f64::INFINITY, f64::min)
}
```

---

## Rotation Number Bound

**Claim:** |tr(ψ)| < 2 for all non-Lagrangian 2-faces.

**Source:** CH2021 Lemma 2.17

**Derivation:**

From the trace formula: tr(ψ_F) = 2⟨n_entry, n_exit⟩

Since n_entry and n_exit are distinct unit normals of adjacent facets:
- They cannot be equal (distinct facets): ⟨n_entry, n_exit⟩ ≠ 1
- They cannot be opposite (convexity prevents this for adjacent facets): ⟨n_entry, n_exit⟩ ≠ -1

Therefore |tr(ψ_F)| < 2 always holds, so ψ_F is elliptic.

The rotation number ρ = arccos(tr(ψ)/2) / 2π is well-defined and in (0, 0.5).

---

## Flow Map is Symplectic

**Claim:** det(A) = 1 for all flow maps.

**Source:** CH2021 Lemma 2.16

**Derivation:**

The flow map A = ψ + r_triv ⊗ t_grad where:
- ψ is the transition matrix (symplectic, det = 1)
- r_triv ⊗ t_grad is a rank-1 matrix

For a 2×2 matrix M and rank-1 perturbation uvᵀ:
```
det(M + uvᵀ) = det(M) · (1 + vᵀ M⁻¹ u)
```

However, the correct argument is that the Reeb flow preserves the symplectic form (fundamental property of Hamiltonian/Reeb dynamics), so any flow map between symplectic trivializations has determinant 1.

**Verification:** This is checked by assertion in the code:
```rust
assert!((flow_map.matrix.determinant() - 1.0).abs() < EPS);
```

---

## Flow Direction Convention

**Source:** CH2021 Definition 2.15

**Convention:** Trivialization uses the EXIT facet's normal.

Per CH2021: "Let ν denote the outward unit normal vector to E" where E is the facet the Reeb flow **points into** (the exit facet).

**TwoFaceData design:**

| Flow direction | entry_normal | exit_normal | transition_matrix |
|----------------|--------------|-------------|-------------------|
| ItoJ (ω > 0)   | nᵢ          | nⱼ          | τ_{nⱼ} ∘ τ_{nᵢ}⁻¹ |
| JtoI (ω < 0)   | nⱼ          | nᵢ          | τ_{nᵢ} ∘ τ_{nⱼ}⁻¹ |

**Design choice (B):** Store flow-aware normals rather than canonical i < j normals. This simplifies the extend_tube code — no flow-direction checks needed when applying transition_matrix.

---

## Minimum Closed Tube Length

**Claim:** A closed tube requires minimum facet sequence length 5.

**Proof:**

A closed tube visits at least 3 distinct facets. For facet sequence [i, j, k, i, j]:
- Length = 5
- Visits facets i, j, k
- Start 2-face = F_{i,j}, end 2-face = F_{i,j} ✓

Length 4 [i, j, i, j] fails:
- Would require flow i→j at F_{i,j}, then j→i at F_{j,i} = F_{i,j}
- But flow direction is fixed by ω(nᵢ, nⱼ): if ω > 0, flow always goes i→j
- By antisymmetry, flow cannot reverse at the same 2-face □
