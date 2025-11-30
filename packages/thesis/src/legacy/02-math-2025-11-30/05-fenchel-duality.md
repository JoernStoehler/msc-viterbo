---
title: Fenchel Duality and Clarke's Functional
summary: Gauge/support duality and dual action principle.
---

Gauge–support duality
- For a convex body \(K\) containing the origin,
  $$g_K(x)^2 \text{ and } \tfrac14 h_K(y)^2$$
  are Fenchel duals: \(g_K(x)^2 = \sup_y (\langle x,y\rangle - \tfrac14 h_K(y)^2)\), and conversely \(\tfrac14 h_K(y)^2 = \sup_x (\langle x,y\rangle - g_K(x)^2)\).
- Equality in Fenchel duality holds iff \(y\in \partial g_K^2(x)\) iff \(x\in \partial \tfrac14 h_K^2(y)\); this characterizes normals vs. contact points on supporting facets.

Clarke’s dual action functional
- On the space \(E=\{z\in W^{1,2}([0,1],\mathbb R^4) : \int_0^1 \langle -J\dot z, z\rangle dt = 1, \int_0^1 \dot z = 0\}\), define
  $$I_K(z) = \frac14 \int_0^1 h_K^2(-J\dot z(t))\,dt.$$
- Dual principle (Clarke, Abbondandolo–Majer): critical points of \(I_K\) correspond to generalized closed characteristics; moreover
  $$c_{\mathrm{EHZ}}(K) = \Big(2\sup_{z\in E} \int_0^1 \langle -J z, \dot z\rangle dt\Big)^{-1} = \inf_{z\in E} I_K(z).$$
 - The Euler–Lagrange equation says \(-J\dot z(t)\in \partial(\tfrac14 h_K^2)(-J\dot z(t))\) and gives the facet-velocity description used in HK2017/CH2021.

Polytope specialization
- For polytopes, \(h_K\) is piecewise linear; \(I_K\) becomes an integral of a piecewise quadratic form in \(\dot z\), and minimizing loops can be taken piecewise affine (HK2017 uses this to get the combinatorial formula).
