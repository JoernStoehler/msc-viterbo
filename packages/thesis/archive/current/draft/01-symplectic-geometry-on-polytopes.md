# Symplectic Geometry on Convex Polytopes (Draft)

This file fixes the non-smooth symplectic conventions needed by the capacity algorithm. All terminology is defined before use; every nontrivial claim is cited or proved. Inputs with Lagrangian 2-faces are rejected.

## 0. Ambient setup and standing assumptions
- Coordinates and inner product: \(\mathbb{R}^4\) with column vectors \((q_1,q_2,p_1,p_2)^T\) and Euclidean inner product \(\langle\cdot,\cdot\rangle\).
- Symplectic data: \(\omega_0 = dq_1\wedge dp_1 + dq_2\wedge dp_2\); complex structure \(J = \begin{pmatrix}0&-I\\ I&0\end{pmatrix}\) so \(\omega_0(u,v)=\langle Ju,v\rangle\); Liouville form \(\lambda_0 = \tfrac12\sum_{i=1}^2(p_i\,dq_i - q_i\,dp_i)\).
- Polytope \(K\): convex, compact, star-shaped, given in H-rep by outward unit facet normals \(n_f\) with supports \(b_f>0\), and \(0\in\operatorname{int}K\).
- Non-Lagrangian ridges: for every ridge (2-face) \(i\), \(\omega_0|_{T_i}\neq 0\); inputs violating this are rejected.

## 1. Glossary and notation
- **Facet** \(F\): \(F = K\cap H_F\) with supporting hyperplane \(H_F=\{x:\langle n_F,x\rangle=b_F\}\), unit \(n_F\), support \(b_F>0\).
- **Ridge** \(i\): intersection of two distinct facets, \(i=F\cap G\). Co-facet notation: if a ridge \(j\subset F\cap G\), write \(G(j,F)\) for the facet \(G\neq F\) with \(j=F\cap G\).
- **Gauge / Hamiltonian**: \(g_K(x)=\inf\{\lambda\ge0: x\in \lambda K\}\); \(H(x)=g_K(x)^2\).
- **Facet Hamiltonian velocity**: \(p_F := (2/b_F) J n_F\) (HK2019, Prop. 3.6); all facet segments are parametrized with \(\dot x = p_F\).
- **Ridge charts**: for ridge \(i\), fix an orthonormal, \(\omega_0\)-positive basis of \(T_i\); \(\pi_i: i\to A_i\subset\mathbb{R}^2\) the chart, \(\Xi_i\) its inverse affine map.
- **Facet-simple**: a polygonal orbit whose visited facets have no repetitions.
- **Rotation accumulation**: for an edge map with linear part \(M_{ij}\) in ridge charts, write \(M_{ij}=R_{ij}S_{ij}\) (polar factor, \(R_{ij}\in\mathrm{SO}(2)\)), set \(\rho_{ij}=\operatorname{arg}(R_{ij})/\pi\in[0,1)\); along a cycle, total rotation is the sum of the \(\rho_{ij}\).

## 2. Core definitions
- **Subdifferential on \(\partial K\)** (HK2019, lines 216–224): if \(x\in F_1\cap\cdots\cap F_m\) with normals \(n_i\), supports \(b_i\), then
  \[\partial H(x)=\operatorname{conv}\{ 2 n_i / b_i : i=1,\dots,m \}.\]
- **Generalized Hamiltonian trajectory** (HK2019, §2.2): an absolutely continuous \(\gamma:[0,T]\to\partial K\) with \(\dot\gamma(t)\in J\partial H(\gamma(t))\) for a.e. \(t\).
- **Closed characteristic**: the image of such a trajectory with \(\gamma(0)=\gamma(T)\) and not everywhere constant; parametrizations with the same image are identified. Any chosen parametrization must satisfy the inclusion above.
- **Action**: for any representative \(\gamma\), \(A(\gamma)=\int_0^T \lambda_0(\dot\gamma(t))\,dt = \int_\gamma \lambda_0\), independent of reparametrization. Because \(H\equiv1\) on \(\partial K\), the usual \(+\int H\) term is constant and omitted.
- **Facet segment action (lemma).** Let \(x\in F\) and \(\gamma(t)=x+t p_F\) until the next facet is hit. Then \(\gamma(t)\in H_F\) for all \(t\), and for any \(\tau>0\),
  \[A(\gamma|_{[0,\tau]})=\tau.\]
  *Proof:* \(\langle \gamma(t), n_F\rangle=b_F\) so \(\lambda_0(p_F)=\tfrac12\langle J\gamma(t),p_F\rangle=\tfrac12\langle Jx,(2/b_F)J n_F\rangle=\langle x,n_F\rangle/b_F=1\); integrate over \([0,\tau]\).

## 3. Imported theorems (restated; proofs in cited sources)
- **Polygonal representative** (HK2019, Lemmas 3.1–3.5): any generalized closed characteristic on \(\partial K\) is homotopic, through generalized trajectories, to one whose velocity is piecewise constant with values in \(\{p_F\}\).
- **Simple-loop theorem** (HK2019, Thm. 1.5): there exists a minimal-action closed characteristic whose velocity pieces are positive multiples of \(p_F\) and each facet appears at most once (facet-simple).
- **Rotation/CZ bound (smooth case)** (CH2021, Prop. ehwz(b)): for a compact strictly convex smooth domain in \(\mathbb{R}^4\), there is an action minimiser with \(\rho\le2\); if nondegenerate then \(\rho<2\) and \(\mu_{\mathrm{CZ}}=3\).
- **Smooth–polygonal correspondence** (CH2021, Thms. combtosmooth and smoothtocomb): for a symplectic polytope (all ridges non-Lagrangian), nondegenerate polygonal orbits with bounded \(\rho\) correspond to Reeb orbits on smoothings with the same action, rotation number, and CZ index, and conversely any bounded-\(\rho\) sequence of Reeb orbits on smoothings has a subsequence limiting to a polygonal orbit (Type 1 or 2) with matching action and, if Type 1, matching \(\rho\) and CZ.

## 4. Local geometric facts
- **Ridge orientation** (HK2019, Lemma 3.4): for a non-Lagrangian ridge \(i=F\cap G\), exactly one of \(p_F, p_G\) points into \(i\) and the other points out; equivalently \(\langle n_F, J n_G\rangle\neq0\).
- **Exit-time condition:** for a ridge pair \(i\xrightarrow{F} j\) inside facet \(F\), the forward exit time to co-facet \(G(j,F)\) is
  \[\tau_{ij}(x)=\frac{b_{G(j,F)}-\langle n_{G(j,F)},x\rangle}{\langle n_{G(j,F)}, p_F\rangle},\quad \tau_{ij}(x)>0,\]
  well-defined whenever \(\langle n_{G(j,F)}, p_F\rangle>0\). Uniqueness of the first exit holds off a measure-zero set by convexity and the non-Lagrangian ridge hypothesis.
- **Per-edge rotation increment:** in fixed ridge charts, for the affine first-hit map with linear part \(M_{ij}\), write \(M_{ij}=R_{ij}S_{ij}\) (polar factor, \(R_{ij}\in\mathrm{SO}(2)\)). Define \(\rho_{ij}=\operatorname{arg}(R_{ij})/\pi\in[0,1)\); accumulated rotation along a cycle is the sum of the \(\rho_{ij}\).

## 5. Exclusions
- Lagrangian ridges (\(\omega_0|_{T_i}=0\)).
- Higher-order degeneracies (e.g. triple intersections, non-unique first exits). Numerical detection of such cases should trigger rejection rather than inference.

## 6. References
- HK2019: P. Haim-Kislev, “On the symplectic size of convex polytopes”, arXiv:1712.03494v3. Uses: lines 216–224 (subdifferential), Prop. 3.6 (facet velocity), Lemmas 3.1–3.5 (polygonal representative), Lemma 3.4 (ridge orientation), Thm. 1.5 (simple loop).
- CH2021: J. Chaidez, M. Hutchings, “Computing Reeb dynamics on 4d convex polytopes”, arXiv:2008.10111v2. Uses: Prop. ehwz(b) (rotation/CZ bound), Thms. combtosmooth and smoothtocomb (smooth–polygonal correspondence).
