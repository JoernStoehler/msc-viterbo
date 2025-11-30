---
title: Closed Characteristics and Hamiltonian Orbits
summary: Smooth and polytope settings; normal cones; generalized closed characteristics.
---

Smooth hypersurfaces  
- For a smooth star-shaped hypersurface \(\Sigma=\partial X\subset\mathbb R^4\), the Reeb vector field of \(\lambda=\lambda_0|_\Sigma\) satisfies \(\lambda(R)=1,\ d\lambda(R,\cdot)=0\). A **(parameterized) closed characteristic** is a periodic Reeb orbit; its action equals its period (Section 4). See [@EkelandHofer1990; @HoferZehnder1990].

Normal cones and generalized characteristics on convex bodies  
- For convex \(K\) (possibly non-smooth), the outward normal cone at \(x\in\partial K\) is
  $$N_K(x)=\{v\mid \langle y-x,v\rangle\le 0\ \forall y\in K\}.$$
- The Hamiltonian \(H=g_K^2\) has subgradient \(\partial H(x)=2\,g_K(x)\,\partial g_K(x)\). The **Hamiltonian (generalized) closed characteristics** are \(\gamma\in W^{1,2}(\mathbb T,\mathbb R^4)\) with period \(T>0\) and
  $$\dot\gamma(t) \in J\,N_K(\gamma(t)) = \operatorname{conv}\{p_i : \gamma(t)\in F_i\}\quad\text{a.e.}$$
  where \(p_i=\tfrac{2}{h_i}J n_i\). This matches Reeb/Hamiltonian dynamics on smooth approximations [@ArtsteinAvidanOstrover2014].

Facet behaviour on polytopes (deterministic consequences)  
- Facet interior: if \(\gamma(t)\) lies in the relative interior of \(F_i\), then \(\dot\gamma(t)=p_i\).  
- Non‑Lagrangian 2‑faces: the velocity is not well-defined on the face itself; the orbit crosses the face, entering and exiting through adjacent facets, in a fixed direction determined by those facets.  
- Lagrangian 2‑faces: the velocity is tangent to the 2‑face (Reeb cone tangent); entry/exit happens through adjacent edges/vertices, not through adjacent facets.  
- These cases separate the combinatorics of admissible vs. non‑admissible (Lagrangian) polytopes used later.

Simple Hamiltonian orbits (single-visit)  
- A **Hamiltonian orbit** is as above.  
- A **simple Hamiltonian orbit** is a Hamiltonian orbit that is piecewise linear with finitely many segments, each segment having constant velocity equal to a single facet velocity \(p_i\), and each facet \(F_i\) is used on at most one segment (single visit). Breakpoints occur only at intersections of facets.  
- HK2017/2024 show that for admissible polytopes an action minimizer can be chosen simple; this justifies restricting the search space to simple Hamiltonian orbits in later sections.

Existence statements we rely on (proved in cited papers; Lean placeholders for now)  
- For admissible polytopes the minimum action is attained (not merely an infimum).  
- There exists a simple Hamiltonian orbit that achieves this minimum action.
