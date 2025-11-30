---
title: Symplectic Preliminaries in Dimension 4
summary: Conventions for \(\omega, J, \lambda\) and basic linear symplectic notions.
---

We work in real dimension \(4\), write points as \(z=(q_1,q_2,p_1,p_2)\), and fix once and for all:

- Standard almost complex structure
  $$
  J = \begin{pmatrix}0 & -I_2 \\ I_2 & 0\end{pmatrix},\qquad J(q_1,q_2,p_1,p_2)=(-p_1,-p_2,q_1,q_2).
  $$
- Symplectic form and Liouville form
  $$\omega(x,y)=\langle Jx,y\rangle= dq_1\wedge dp_1 + dq_2\wedge dp_2,\qquad
    \lambda = \tfrac12\sum_{i=1}^2 (q_i\,dp_i - p_i\,dq_i).$$
- Euclidean inner product \(\langle\cdot,\cdot\rangle\) and norm \(|\cdot|\). We identify \(\mathbb R^4\simeq\mathbb C^2\) when convenient but keep \(\mathbb R^4\) as the primary model.

Conventions
- Signs follow HK2017/CH2021: \(\omega(x,y)=\langle Jx,y\rangle\); the action definition below uses this sign.
- A 2-plane \(L\subset\mathbb R^4\) is **Lagrangian** if \(\omega|_L=0\); examples: \(\mathbb R^2_{q}\times\{0\}\) and \(\{0\}\times \mathbb R^2_p\).
- Symplectic linear maps are those preserving \(\omega\); the standard linear symplectic group is \(\mathrm{Sp}(4,\mathbb R)\).
