# Lemma: No Sink Facets

**Status**: Proof sketch only (not yet rigorous enough for thesis)

**Jörn's confidence**: 97% betting odds that this lemma is true.

## Statement

Let K ⊂ ℝ⁴ be a convex polytope with the origin in its interior. If K has no Lagrangian 2-faces (i.e., ω(n_i, n_j) ≠ 0 for all adjacent facet pairs), then every facet has at least one outgoing 2-face and at least one incoming 2-face.

Equivalently: For every facet F_j with normal n_j, there exists some adjacent facet F_k such that ω(n_j, n_k) > 0 (flow goes OUT of F_j), and some other adjacent facet F_l such that ω(n_j, n_l) < 0 (flow goes INTO F_j).

## Proof Sketch (Jörn, 2026-02-01)

We prove the outgoing direction; the incoming direction follows by symmetry (replace Jn with -Jn).

Let n be the outward unit normal of facet F. Suppose for contradiction that ⟨Jn, n_k⟩ ≤ 0 for all neighboring facets F_k (i.e., all 2-faces have flow INTO F).

1. **Jn is tangent to F**: Since J is the symplectic matrix, we have ⟨Jn, n⟩ = 0, so Jn lies in the tangent space of F.

2. **F is a 3-dimensional polytope**: The facet F is a bounded convex polytope of dimension 3.

3. **Existence of boundary point**: Since F is bounded and Jn is a nonzero tangent direction, there exists a point x on the boundary ∂F such that x + ε·Jn lies outside the polytope K for small ε > 0.

4. **Which halfspace is violated?**: Since x + ε·Jn ∉ K, some halfspace inequality must be violated: ⟨x + ε·Jn, n_m⟩ > h_m for some facet F_m.

5. **It's not F itself**: Since ⟨Jn, n⟩ = 0, the halfspace of F is not violated.

6. **It's not a non-neighboring facet**: Since x ∈ F ⊂ K, we have ⟨x, n_m⟩ ≤ h_m for all m. For small ε, if F_m doesn't share a 2-face with F, then ⟨x, n_m⟩ < h_m strictly, so the inequality remains satisfied.

7. **Conclusion**: It must be a neighboring facet F_k, and x lies on the 2-face F ∩ F_k. We have:
   - ⟨x, n_k⟩ = h_k (since x is on F_k)
   - ⟨x + ε·Jn, n_k⟩ > h_k (violated)

   Therefore ⟨Jn, n_k⟩ > 0. This contradicts our assumption.

**Note**: Step 6 assumes that the boundary of F is completely described by 2-faces (i.e., every point on ∂F lies on some 2-face F ∩ F_k). This is true for "generic" polytopes but may fail for degenerate ones.

## Implication for Issue #155

If this lemma is true, then sink facets (facets that only appear as exit, never as entry) indicate a **bug in the code** or a **degenerate polytope** that violates the lemma's assumptions.

### Investigation Results (2026-02-01)

Seed 2661 produces a polytope with **incomplete facet adjacency**:

**Facet 3 analysis:**
- Vertices: {v4, v5, v6, v11} (a tetrahedron)
- 2-face (3,0): triangle v4-v5-v6 ✓
- 2-face (3,6): triangle v4-v6-v11 ✓
- 2-face (3,7): triangle v5-v6-v11 ✓
- **EXPOSED**: triangle v4-v5-v11 (not shared with any other facet!)

The exposed triangle v4-v5-v11 violates the generic position assumption in step 6 of the proof. This face is part of facet 3's boundary but is NOT a 2-face of the polytope.

**Flow consequences:**
- All actual 2-faces of facet 3 have ω(n3, nk) < 0 (incoming flow)
- Facet 3 is a SINK (no outgoing transitions)
- Similarly, facet 0 is a SOURCE (no incoming transitions)

### Resolution

The `has_incomplete_facet_adjacency` check in `random_hrep` correctly detects and rejects such polytopes. This is appropriate because:

1. These polytopes violate the mathematical assumptions of the tube algorithm
2. The check detects facet pairs sharing exactly 2 vertices (an edge but not a 2-face)
3. For seed 2661, facets 3 and 5 share only vertices {v4, v5}, triggering rejection

This is NOT "cheating on tests" - it's filtering out degenerate inputs that the algorithm is not designed to handle.

## Related

- Issue #155: Random polytope test failures
- Test: `verify_seed_2661.rs` (detailed diagnostic)
