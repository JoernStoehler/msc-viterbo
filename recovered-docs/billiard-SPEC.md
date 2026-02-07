# billiard — Minkowski Billiard Algorithm for Lagrangian Products

**Status:** Draft (algorithm design phase)

## Purpose

Compute EHZ capacity for Lagrangian products K_q × K_p ⊂ ℝ⁴ where K_q, K_p ⊂ ℝ² are convex polygons.

This is a specialized algorithm that exploits the Lagrangian product structure to achieve polynomial complexity O((E_q + E_p)^6), compared to the factorial O(F!) complexity of HK2017.

## Theoretical Foundation

**Rudolf 2022, Theorem 1.1:**
```
c_EHZ(K_q × K_p) = min_{q ∈ M_{n+1}(K_q, K_p)} ℓ_{K_p}(q)
```
where M_{n+1} = closed Minkowski billiard trajectories with ≤ n+1 bouncing points.

For n=2 (4D): search over **2-bounce and 3-bounce** orbits only.

**Key insight:** Rudolf's reflection rule q_{j+1} - q_j ∈ N_{K_p}(p_j) is equivalent to the differential inclusion for Reeb orbits. No new theory needed beyond what's used in HK2017/Tube.

## Algorithm Design

### 3-Bounce Orbit Structure

A 3-bounce orbit has 6 breakpoints alternating constant-q and constant-p segments:
```
(q₁,p₁) → (q₁,p₂) → (q₂,p₂) → (q₂,p₃) → (q₃,p₃) → (q₃,p₁) → (q₁,p₁)
```

Variables: 3 points q₁,q₂,q₃ ∈ ∂K_q and 3 points p₁,p₂,p₃ ∈ ∂K_p.
Each point is (edge_index: usize, position: f64 ∈ [0,1)).

### Reflection Constraints

For each transition (e.g., q₁ → q₂ while p = p₂):

**Case: p₂ on edge interior**
- Normal cone N_{K_p}(p₂) = ℝ₊ · n_e (1D, single outward normal)
- Constraint: q₂ - q₁ = t · (2/h) n_e with t ≥ 0
- This is a **linear equality** (direction fixed) plus sign constraint

**Case: p₂ at vertex (intersection of edges L, R)**
- Normal cone N_{K_p}(p₂) = ℝ₊ · conv{n_L, n_R} (2D cone)
- Constraint: q₂ - q₁ = t_L · (2/h_L) n_L + t_R · (2/h_R) n_R with t_L, t_R ≥ 0
- This is **linear inequalities**

### Objective

Minimize action = Σ(t_L + t_R + ...) = sum of Reeb vector coefficients.

This equals the orbit's period (since α(R) = 1 by Reeb normalization).

### Algorithm Outline

```
1. COMBINATORIAL OUTER LOOP: For each configuration
   - Which edge of K_q does each qᵢ lie on? → E_q³ choices
   - Which edge of K_p does each pᵢ lie on? → E_p³ choices
   - For each of 6 bounce points: vertex or edge-interior? → 2⁶ sub-choices

2. LP INNER PROBLEM: For each configuration, solve:
   - Variables: 6 edge-position params + 12 time coefficients (t_L, t_R per transition)
   - Constraints: reflection rules as linear (in)equalities, t ≥ 0
   - Objective: minimize Σ tᵢ = action

3. RETURN: Global minimum action and corresponding orbit witness
```

### Uniform LP Formulation

To avoid heterogeneous LP structures, always use (t_L, t_R) per transition:
- For edge-interior: add constraint t_L = 0 (or t_R = 0), using only true normal
- For vertex: both t_L, t_R free

This gives fixed variable count (18 = 6 positions + 12 times) with uniform constraint matrix. Only which t_L = 0 constraints are active varies per configuration.

The "fake edge" framing: pretend there are always 2 adjacent edges at each bounce point, but one has zero time allocation for edge-interior points.

### Complexity

Naive: O(E_q³ · E_p³ · 2⁶) LP solves, each O(1) size.

For typical polygons (E ~ 3-10): this is thousands of small LPs, very fast.

Compare HK2017: O(F!) = O((E_q · E_p)!) which is factorial in the facet count.

## Open Questions

1. **Vertex-only orbits:** Can we prove the minimum-action orbit always has all bounces at vertices? This would eliminate the 2⁶ factor and simplify to pure combinatorial search.

2. **Exact LP constraints:** Need to derive the complete constraint matrix including closure and geometric compatibility.

3. **2-bounce orbits:** Simpler structure (4 breakpoints, 2 q-values, 2 p-values). Should be handled as special case.

4. **Numerical considerations:** LP solver choice (use existing Rust LP crate?), tolerances for near-vertex points, degeneracy handling.

## API Sketch

```rust
pub struct LagrangianProduct {
    pub k_q: Polygon,  // 2D polygon in q-space
    pub k_p: Polygon,  // 2D polygon in p-space
}

pub struct BilliardWitness {
    pub q_points: [Point2; 3],  // or 2 for 2-bounce
    pub p_points: [Point2; 3],
    pub times: Vec<f64>,        // Reeb coefficients
}

pub fn capacity(polytope: &LagrangianProduct) -> (f64, BilliardWitness);
```

## Dependencies

- `geom` crate for Polygon representation
- LP solver (TBD: clarsiux? minilp? or hand-roll for this small problem?)

## Testing Strategy

Per Jörn's testing philosophy:
- Capacity axioms (symplectomorphism invariance, monotonicity, scaling)
- Continuity (nearby polygons → nearby capacities)
- Literature values (square×square, pentagon×pentagon from HK-O 2024)
- Cross-validate against HK2017 on Lagrangian products
- Orbit properties (closed, action = capacity, breakpoints on boundary, etc.)

## Related Issues

- #92: Complete billiard algorithm section in thesis
- #94: Debug triangle×triangle discrepancy (billiard=3.0 vs hk2017=1.5)
- #93: Implement comprehensive billiard validation test suite
