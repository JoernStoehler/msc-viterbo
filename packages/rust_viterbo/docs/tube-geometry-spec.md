# Tube Geometry Specification

This document specifies the geometric data and formulas needed for the tube-based capacity algorithm.
It uses the language/conventions of the thesis and provides a dictionary to CH2021 where relevant.

**Status:** Draft, pending review.

## 1. Conventions (locked, from thesis)

- Coordinates: (q₁, q₂, p₁, p₂)
- Almost complex structure: J(q,p) = (-p, q)
- Symplectic form: ω(x,y) = ⟨Jx, y⟩
- Polytope H-rep: K = ∩ᵢ {x : ⟨nᵢ, x⟩ ≤ hᵢ} with outward unit normals nᵢ, heights hᵢ > 0

**Notation for faces:**
- **Facets (3-faces):** Eᵢ = {x ∈ K : ⟨nᵢ, x⟩ = hᵢ}
- **2-faces:** Fᵢⱼ = Eᵢ ∩ Eⱼ (when 2-dimensional)

## 2. Basic Objects

### 2.1 Facets (3-faces)

A **facet** Eᵢ is a 3-dimensional face of K, defined by:
```
Eᵢ = {x ∈ K : ⟨nᵢ, x⟩ = hᵢ}
```

The **Reeb velocity** on facet Eᵢ is:
```
vᵢ = (2/hᵢ) J nᵢ
```

### 2.2 2-Faces

A **2-face** Fᵢⱼ is the intersection of two facets Eᵢ ∩ Eⱼ when that intersection is 2-dimensional.

A 2-face Fᵢⱼ is **Lagrangian** iff ω(nᵢ, nⱼ) = 0.

A 2-face Fᵢⱼ is **non-Lagrangian** iff ω(nᵢ, nⱼ) ≠ 0.

### 2.3 Flow Direction

For a non-Lagrangian 2-face Fᵢⱼ, the Reeb flow crosses the 2-face in a definite direction:

- If ω(nᵢ, nⱼ) > 0: flow crosses from Eᵢ into Eⱼ
- If ω(nᵢ, nⱼ) < 0: flow crosses from Eⱼ into Eᵢ

**Proof sketch:** The velocity vᵢ = (2/hᵢ) J nᵢ points into the half-space {⟨nⱼ, x⟩ < hⱼ} iff ⟨J nᵢ, nⱼ⟩ > 0 iff ω(nᵢ, nⱼ) > 0.

## 3. Affine Flow Map Between 2-Faces

### 3.1 Setup

Consider a trajectory that:
- Starts at point p on 2-face Fᵢₖ (= Eᵢ ∩ Eₖ)
- Flows along facet Eₖ with velocity vₖ
- Ends at point p' on 2-face Fₖⱼ (= Eₖ ∩ Eⱼ)

### 3.2 Time to Reach Next 2-Face

The trajectory follows p' = p + t · vₖ. It reaches Fₖⱼ when ⟨nⱼ, p'⟩ = hⱼ.

Solving:
```
⟨nⱼ, p + t · vₖ⟩ = hⱼ
t = (hⱼ - ⟨nⱼ, p⟩) / ⟨nⱼ, vₖ⟩
```

Since vₖ = (2/hₖ) J nₖ:
```
t(p) = (hⱼ - ⟨nⱼ, p⟩) / ((2/hₖ) ⟨nⱼ, J nₖ⟩)
     = (hⱼ - ⟨nⱼ, p⟩) / ((2/hₖ) ω(nₖ, nⱼ))
     = hₖ (hⱼ - ⟨nⱼ, p⟩) / (2 ω(nₖ, nⱼ))
```

This is an **affine function** of p.

### 3.3 Flow Map

The flow map φ: Fᵢₖ → Fₖⱼ is:
```
φ(p) = p + t(p) · vₖ
```

This is an **affine map**. Its linear part is:
```
Tφ: T(Fᵢₖ) → T(Fₖⱼ)
```

### 3.4 Action Increment

The action increment equals the time increment:
```
A_inc(p) = t(p)
```

This is an **affine function** of p.

## 4. Rotation Number

### 4.1 Quaternion Structure

Define quaternion matrices i, j, k ∈ O(4) satisfying:
- i² = j² = k² = -I
- ij = k, jk = i, ki = j
- **i = J** (our almost complex structure)

In (q₁, q₂, p₁, p₂) coordinates:
```
i = J = | 0  0 -1  0 |
        | 0  0  0 -1 |
        | 1  0  0  0 |
        | 0  1  0  0 |

j =     | 0 -1  0  0 |
        | 1  0  0  0 |
        | 0  0  0  1 |
        | 0  0 -1  0 |

k =     | 0  0  0 -1 |
        | 0  0  1  0 |
        | 0 -1  0  0 |
        | 1  0  0  0 |
```

**TODO:** Verify these matrices satisfy the quaternion relations with our J convention.

### 4.2 Trivialization of a 2-Face

Let F = Fᵢⱼ = Eᵢ ∩ Eⱼ be a non-Lagrangian 2-face. Assume (by relabeling if needed) that ω(nᵢ, nⱼ) > 0, so flow crosses F from Eᵢ into Eⱼ.

The 2-face F has two adjacent facets: Eᵢ (which flow is leaving) and Eⱼ (which flow is entering).

Define two trivializations τ_F, τ'_F: TF → ℝ²:

**τ_F** (using the normal of the facet that flow is **entering**):
```
τ_F(V) = (⟨V, j nⱼ⟩, ⟨V, k nⱼ⟩)
```

**τ'_F** (using the normal of the facet that flow is **leaving**):
```
τ'_F(V) = (⟨V, j nᵢ⟩, ⟨V, k nᵢ⟩)
```

**Claim:** Both τ_F and τ'_F are symplectic isomorphisms (TF, ω|_TF) → (ℝ², ω₀), where ω₀ is the standard symplectic form on ℝ².

### 4.3 Transition Matrix

The **transition matrix** of 2-face F is:
```
ψ_F = τ_F ∘ (τ'_F)⁻¹ : ℝ² → ℝ²
```

**Claim:** ψ_F ∈ Sp(2) (i.e., preserves the standard symplectic form on ℝ²).

**Claim:** ψ_F is **positive elliptic**, meaning:
1. |Tr(ψ_F)| < 2 (so eigenvalues are on the unit circle, not real)
2. For all v ∈ ℝ² \ {0}: det([v, ψ_F v]) > 0 (positive orientation)

### 4.4 Rotation Increment

**Definition (positive elliptic rotation):** For a positive elliptic matrix A ∈ Sp(2) with |Tr(A)| < 2:
- A has eigenvalues e^{±2πiθ} for a unique θ ∈ (0, 1/2)
- θ is computed as: θ = arccos(Tr(A)/2) / (2π)

The **rotation increment** at 2-face F is:
```
ρ(F) = θ where ψ_F has eigenvalues e^{±2πiθ}, θ ∈ (0, 1/2)
```

### 4.5 Additivity of Rotation

**Key fact:** Rotation is **additive** in the universal cover Sp̃(2).

The universal cover Sp̃(2) is a group with an additive rotation homomorphism ρ: Sp̃(2) → ℝ. For a sequence of 2-face crossings F₁, F₂, ..., Fₘ, the total rotation is simply:
```
ρ_total = ρ(F₁) + ρ(F₂) + ... + ρ(Fₘ)
```

This follows from the group structure of Sp̃(2) and the fact that each ψ_F is positive elliptic with rotation in (0, 1/2). The bounds from CH2021 Proposition A.4 (ρ(B̃) ≤ ρ(ÃB̃) ≤ ρ(B̃) + 1/2 when ρ(Ã) ∈ (0, 1/2)) are consistent with simple additivity.

**Note:** We do NOT need to track the matrix product M = ψ_Fₘ ⋯ ψ_F₁ or its classification. The rotation is simply the sum of individual rotation increments.

## 5. Tube Data Structure

A **tube** represents the set of trajectories consistent with a combinatorial path. Search nodes are indexed by facet sequences.

### 5.1 Node Indexing

A search node is a sequence of facet indices (1, 2, ..., k, k+1) where:
- The trajectory starts on 2-face F₁₂ = E₁ ∩ E₂
- It then flows along E₂, crossing F₂₃
- Then flows along E₃, crossing F₃₄
- ...and so on

The **combinatorics** of a tube at node (1, 2, ..., k, k+1) are:
```
Comb(tube) = [F₁₂, F₂₃, ..., Fₖ,ₖ₊₁]
```

### 5.2 Tube Fields

| Field | Type | Description |
|-------|------|-------------|
| P_start | Polygon in TF₁₂ | Set of valid starting points |
| P_end | Polygon in TFₖ,ₖ₊₁ | Set of valid ending points |
| ψ | Affine map | Flow map from P_start to P_end |
| A | Affine function on P_end | Action as function of endpoint |
| ρ | Real number | Total rotation so far (in turns) |

### 5.3 Root Tube

For root node (1, 2) representing trajectories starting on 2-face F₁₂:
```
P_start = P_end = F₁₂  (the full 2-face)
ψ = identity
A = 0  (constant function)
ρ = ρ(F₁₂)  (rotation from crossing the starting 2-face)
```

**Rationale:** Including ρ(F₁₂) in the root enables earlier pruning. At closure, we subtract ρ(F₁₂) to avoid double-counting (see Section 6.2).

### 5.4 Extension

To extend from node (1, ..., k, k+1) to (1, ..., k, k+1, k+2):

**Setup:**
- Current ending 2-face: Fₖ,ₖ₊₁ = Eₖ ∩ Eₖ₊₁
- New ending 2-face: Fₖ₊₁,ₖ₊₂ = Eₖ₊₁ ∩ Eₖ₊₂
- The trajectory flows along facet Eₖ₊₁, crossing 2-face Fₖ₊₁,ₖ₊₂

Let φ be the flow map from Fₖ,ₖ₊₁ to Fₖ₊₁,ₖ₊₂ along facet Eₖ₊₁.

**Update formulas:**
```
P'_end = φ(P_end) ∩ Fₖ₊₁,ₖ₊₂
ψ' = φ ∘ ψ
A'(z) = A(φ⁻¹(z)) + t(φ⁻¹(z))   where t is the time-to-reach function from Section 3.2
ρ' = ρ + ρ(Fₖ₊₁,ₖ₊₂)
```

**Note on rotation:** The rotation increment is for the 2-face being **crossed** (Fₖ₊₁,ₖ₊₂), not the 2-face being left.

**Note:** P_start does not change during extension.

### 5.5 Pruning

A tube can be pruned (discarded) when:
1. **Empty tube:** P_end becomes empty
2. **Rotation cutoff:** ρ > 2 (no minimum-action orbit can have rotation > 2 turns)

## 6. Simplicity and Closure

### 6.1 Simplicity Constraint

An orbit is **simple** if it visits each facet at most once before returning to the start.

**Combinatorial criterion:** A tube at node (1, 2, ..., k, k+1) represents simple orbits iff all facet indices 1, 2, ..., k+1 are **distinct**.

During search, only extend to facet indices not already in the sequence.

### 6.2 Immediately Closable Tubes

A tube at node (1, 2, ..., k, k+1) is **immediately closable** when Eₖ₊₁ = E₁.

In this case:
- The trajectory is currently on 2-face Fₖ,₁ = Eₖ ∩ E₁
- It flows along E₁ back toward the starting 2-face F₁₂ = E₁ ∩ E₂
- The only valid next step is to close the orbit by crossing F₁₂

An immediately closable tube can either:
1. **Close:** If the flow direction allows returning to F₁₂ (i.e., ω(n₁, n₂) has the right sign)
2. **Be discarded:** If the flow cannot return to F₁₂

### 6.3 Closed Tubes

A tube **closes** when it returns to the starting 2-face. This happens at node (1, 2, ..., k, 1, 2) where:
- Eₖ = E₁ (just visited first facet)
- Eₖ₊₁ = E₂ (about to cross back to starting 2-face F₁₂)

For a closed tube:
- The combinatorics form a cycle: F₁₂ → F₂₃ → ... → Fₖ₋₁,₁ → F₁₂
- The 2-face F₁₂ appears at both the start and end

**Cyclic rotation:** To compute the rotation of the closed orbit:
```
ρ_cyclic = ρ_tube - ρ(F₁₂)
```

This subtracts the double-counted rotation from crossing F₁₂ (once at root initialization, once at closure).

### 6.4 Action of Closed Orbit

For a closed tube, valid orbits must have **starting point = ending point** (periodicity).

The periodic points are the fixed points of the total flow map ψ: P_start → P_end. At a fixed point p:
```
A_orbit = A(p)
```

This requires intersecting the polygon P_end with the line/hyperplane where ψ(p) = p, then evaluating the action function A at those points.

## 7. Dictionary: Thesis ↔ CH2021

| Thesis | CH2021 | Notes |
|--------|--------|-------|
| Facet Eᵢ | 3-face E | |
| 2-face Fᵢⱼ | 2-face F | |
| Reeb velocity vᵢ | Reeb vector field R_E | |
| Tube | Linear flow (D, φ, f) | |
| Flow map φ | Flow map φ_e | |
| Action increment | Action function f_e | |
| Rotation increment ρ(F) | ρ(ψ̃_F) | Single 2-face |
| Search tree node | Path p in flow graph Γ | |
| τ_F (entry trivialization) | τ_F | Uses "entry" facet normal |
| τ'_F (exit trivialization) | τ'_F | Uses "exit" facet normal |
| Transition matrix ψ_F | Transition matrix ψ_F | τ_F ∘ (τ'_F)⁻¹ |

## 8. Open Questions / TODOs

1. ~~**Verify quaternion matrices:**~~ ✓ Verified in `rust_viterbo_geom::quaternion` module with unit tests.

2. **Prove claims in Section 4:** The claims that τ_F, τ'_F are symplectic and that ψ_F is positive elliptic are stated without proof. These follow from convexity of K and the quaternion structure, but should be verified.

3. **Numerical stability:** How to handle near-Lagrangian 2-faces where ω(nᵢ, nⱼ) ≈ 0?

4. **2D polygon representation:** Choose a basis for each 2-face tangent space to represent P_end as a 2D polygon. Options:
   - Use τ_F or τ'_F to identify TF with ℝ²
   - Use an arbitrary orthonormal basis of TF

5. **Explicit formula for (τ'_F)⁻¹:** Needed to compute ψ_F = τ_F ∘ (τ'_F)⁻¹. Since τ'_F: TF → ℝ² is given by τ'_F(V) = (⟨V, j nᵢ⟩, ⟨V, k nᵢ⟩), we need (τ'_F)⁻¹: ℝ² → TF.

6. **Minimum action search:** For closed tubes, describe the algorithm to find the minimum action over all periodic points.
