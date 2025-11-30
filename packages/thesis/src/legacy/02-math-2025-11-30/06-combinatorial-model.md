---
title: Combinatorial Model on Polytopes
summary: Facet velocities, simple orbits, HK combinatorial formula.
---

Facet velocities
- For each facet \((n_i,h_i)\), velocity \(p_i = \tfrac{2}{h_i} J n_i\).

Hamiltonian orbits on polytopes
- **Hamiltonian orbit:** \(\gamma\in W^{1,2}(\mathbb T,\mathbb R^4)\), period \(T>0\), with \(\dot\gamma(t)\in\operatorname{conv}\{p_i: \gamma(t)\in F_i\}\) a.e.
- **Simple Hamiltonian orbit (single-visit):** piecewise linear with finitely many segments; on each segment \(\dot\gamma=p_i\) for a single facet \(F_i\); each facet is used on at most one segment; breakpoints lie at facet intersections.
- We distinguish this analytic object from the **combinatorial word** (facet indices + positive durations, with no dynamics); the algorithm enumerates words, then certifies Hamiltonian realizability.
- HK2017 show an action minimizer can be chosen simple; CH2021 sharpen rotation bounds for non‑Lagrangian polytopes.

HK combinatorial formula (4D specialization)
Given facets \((n_i,h_i)_{i=1}^F\) of a convex polytope \(K\subset\mathbb R^4\), define
- Coefficients \(\beta_i\ge 0\) with constraints \(\sum_i \beta_i h_i = 1\), \(\sum_i \beta_i n_i = 0\).
- Permutations \(\sigma\in S_F\).
Then [@HK2017]:
$$
 c_{\mathrm{EHZ}}(K)
 = \frac12\Bigg[\max_{\sigma,\,\beta}\sum_{j<i}\beta_{\sigma(i)}\beta_{\sigma(j)}\,\omega(n_{\sigma(i)}, n_{\sigma(j)})\Bigg]^{-1}.
$$
In the centrally symmetric case, the factor is \(\tfrac14\) with paired normals.

Existence of simple minimizers
- HK2017 Theorem 1.5 (specialized to 4D): there exists an action-minimizing closed characteristic whose derivative is piecewise constant, using each \(p_i\) at most once. This justifies restricting the minimization to simple combinatorial orbits.
- CH2021 refine: for non-Lagrangian polytopes, any action minimizer has combinatorial rotation number \(\rho\le 2\) and lies in a finite search set bounded by face-complexity constants.

Computational remarks
- The feasible set \(\{\beta\}\) is a finite-dimensional polytope; permutations are finite. The formula is amenable to exact or numeric search and underlies the algorithmic chapter that follows.
- In practice we enumerate permutations up to symmetries (central symmetry, facet relabeling), solve the linear constraints on \(\beta\), and evaluate the quadratic form in \(\omega(n_i,n_j)\).
