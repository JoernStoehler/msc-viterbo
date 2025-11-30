---
title: Convex Bodies and Polytopes
summary: Definitions of polytopes, admissibility, faces, and Lagrangian vs non-Lagrangian 2-faces.
---

Convex bodies and support/gauge
- A **convex body** \(K\subset\mathbb R^4\) is compact, convex, with nonempty interior.
- Support function: \(h_K(v)=\sup_{x\in K}\langle x,v\rangle\).
- Gauge (Minkowski functional): \(g_K(v)=\inf\{r>0: v\in rK\}\); polar body \(K^\circ=\{y: h_K(y)\le 1\}\). Gauge and support are Fenchel dual up to the quadratic factor (Section 5).

Polytopes and facets
- A **polytope** is an intersection of finitely many half-spaces
  $$K = \bigcap_{i=1}^F \{x\in\mathbb R^4\mid \langle x,n_i\rangle \le h_i\},\qquad |n_i|=1,\ h_i>0.$$
- The (nonempty) intersection with a supporting hyperplane is a **face**. A 3-face is a **facet**; a 2-face is a **ridge**. We only call nonempty sets faces.
- We assume an **irreducible** description (no redundant facets) unless stated.

Admissible and non-Lagrangian polytopes
- An **admissible polytope** is a full-dimensional convex polytope with \(0\in\mathrm{int}(K)\). Translation can enforce this without loss, and we keep the origin to simplify formulas.
- A 2-face is **Lagrangian** if its tangent plane is Lagrangian; otherwise **non-Lagrangian**. A **non-Lagrangian admissible polytope** has no Lagrangian 2-faces.
- HK/CH: non-Lagrangian (“symplectic polytope” in [@CH2021]) gives a well-posed Hamiltonian facet flow (velocities transverse across 2-faces); Lagrangian faces require extra care (not used later today).

Normals, heights, velocities
- For each facet \(F_i\): unit outer normal \(n_i\), height \(h_i=h_K(n_i)\); define **facet velocity**
  $$p_i = \frac{2}{h_i} J n_i.$$
  This is the Hamiltonian/Reeb velocity on the relative interior of \(F_i\) for the Hamiltonian \(H=g_K^2\).

Examples
- Cube, cross-polytope, and regular simplex (simplex has Lagrangian 2-faces).
- HK2024 counterexample facets come from the product of two pentagons; details in Section 8.
