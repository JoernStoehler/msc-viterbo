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

Investigation revealed that seed 2661 produces a polytope where facet 3 has a triangular face (part of its boundary) that is NOT shared with any other facet. This violates the generic position assumption in step 6.

## Related

- Issue #155: Random polytope test failures
- [issue-155-investigation.md](issue-155-investigation.md)
