---
title: Action Functional and EHZ Capacity
summary: Action formula, capacity definitions, continuity from smooth bodies.
---

Action
- For a loop \(\gamma:[0,T]\to\mathbb R^4\),
  $$A(\gamma)=\frac12\int_0^T \langle J\gamma(t),\dot\gamma(t)\rangle\,dt = \int_0^T \lambda(\dot\gamma(t))\,dt.$$
- If \(\gamma\) is a Reeb orbit on a contact-type hypersurface, \(A(\gamma)=T\).
- Orientation reversal negates \(A\); we minimize over positive-action (equivalently, positive-period) parametrizations.

Capacities on convex bodies
- For smooth convex \(K\), the first Ekeland–Hofer capacity, Hofer–Zehnder capacity, and symplectic homology capacity coincide and equal the minimal action of a closed characteristic; denote this common value \(c_{\mathrm{EHZ}}(K)\) [@EkelandHofer1990; @HoferZehnder1990; @AbbondandoloKang; @Irie2014].
- For arbitrary convex \(K\), define \(c_{\mathrm{EHZ}}(K)\) by \(C^0\)-continuity from smooth bodies; by Clarke duality the value still equals the minimal action of a generalized closed characteristic [@ArtsteinAvidanOstrover2014].
- Basic properties: monotone under inclusion, homogeneous of degree 2 under scaling, translation invariant, \(c_{\mathrm{EHZ}}(B(r))=\pi r\), \(c_{\mathrm{EHZ}}(Z(r))=\pi r\).
- Systolic ratio in dimension 4:
  $$\operatorname{sys}(K)=\frac{c_{\mathrm{EHZ}}(K)^2}{2\,\operatorname{vol}(K)}.$$
  Weak Viterbo conjecture claims \(\operatorname{sys}(K)\le 1\) for convex \(K\); HK2024 gives a counterexample.

Examples
- Ball \(B(R)\): \(c_{\mathrm{EHZ}}=\pi R^2\), volume \(=\tfrac12\pi^2 R^4\), systolic ratio \(1\).
- Ellipsoid \(E(a,b)=\{\pi|z_1|^2/a+\pi|z_2|^2/b\le 1\}\): \(c_{\mathrm{EHZ}}=\pi\min(a,b)\).
- Polydisk \(D(R_1)\times D(R_2)\): \(c_{\mathrm{EHZ}}=\pi\min(R_1^2,R_2^2)\).
