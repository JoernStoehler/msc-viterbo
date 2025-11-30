---
title: Examples
summary: Polydisk-like example and HK2024 counterexample.
---

Polydisk sketch
- For \(K = D(R_1)\times D(R_2)\) (or a square-symplectic product polytope approximation), \(c_{\mathrm{EHZ}}(K)=\pi \min(R_1^2,R_2^2)\), volume \(=\pi^2 R_1^2 R_2^2\), systolic ratio \(\le 1\). A polytopal model can be built as a product of squares; details deferred to the algorithm chapter.
- A square \(\times_S\) square approximation keeps facet velocities axis-aligned; the simple minimizer uses two opposite facets, giving action \(\pi \min(R_1^2,R_2^2)\).

HK2024 counterexample [@HK2024]
- Take \(\mathbb R^4 = \mathbb R_q^2 \oplus \mathbb R_p^2\).
- Let \(K\subset\mathbb R_q^2\) be the regular pentagon with unit circumradius, vertices
  $$v_k = (\cos \tfrac{2\pi k}{5},\ \sin \tfrac{2\pi k}{5}),\quad k=0,\dots,4.$$
- Let \(T\subset\mathbb R_p^2\) be \(K\) rotated by \(-\tfrac\pi2\):
  $$w_k = (\cos(-\tfrac\pi2+ \tfrac{2\pi k}{5}),\ \sin(-\tfrac\pi2+ \tfrac{2\pi k}{5})).$$
- Lagrangian product \(P = K\times T\subset\mathbb R^4\). Facet normals are pairs \((n_i,0)\) and \((0,n_j')\) from the two factors; facet velocities follow \(p_i=\tfrac{2}{h_i}Jn_i\).
- Capacity: HK2024 Proposition 1 gives
  $$c_{\mathrm{EHZ}}(P) = 2\cos(\tfrac\pi{10})(1+\cos(\tfrac\pi5)).$$
- Areas: \(\mathrm{area}(K)=\mathrm{area}(T)= \tfrac52\sin(\tfrac{2\pi}{5})\). Systolic ratio
  $$\frac{c_{\mathrm{EHZ}}(P)^2}{2\, \mathrm{vol}(P)} = \frac{\sqrt5+3}{5} > 1,$$
  violating the weak Viterbo conjecture.
- The minimizing characteristic is a 2-bounce Minkowski billiard along a diagonal of the pentagon; its simple Hamiltonian orbit uses two facet velocities once each.
- By Bezdek–Bezdek’s minimal billiard characterization, any other 2-bounce with one vertex on a pentagon edge has the same \(T^\circ\)-length; 3-bounce candidates are longer (HK2024 Sec. 3).

Remarks
- By continuity one obtains smooth convex bodies near \(P\) with the same systolic ratio. The example is central to later algorithm tests and Lean formalization.
