
# Math Background

## Symplectic preliminaries in \(\mathbb{R}^4\)

We write points as \(z=(q_1,q_2,p_1,p_2)\) and fix the standard almost complex structure

\[
J = \begin{pmatrix}0 & -I_2 \\ I_2 & 0\end{pmatrix},\qquad J(q_1,q_2,p_1,p_2)=(-p_1,-p_2,q_1,q_2).
\]

/// admonition | Lemma (Properties of \(J\))
    type: lemma
    attrs: { name: "lem:j-properties" }
\[
    J^2 = -I_4,\qquad
    J^T = -J,\qquad
    \langle Jx, y\rangle = -\langle x, Jy\rangle.
\]
///

The symplectic form and Liouville 1‑form are

\[
\omega = \sum_{i=1}^2 dq_i \wedge dp_i,\qquad
\omega(x,y)=\langle Jx,y\rangle 
\]

\[
\lambda = \tfrac12 \sum_{i=1}^2 (q_i\,dp_i - p_i\,dq_i),\qquad \lambda_z = \langle Jz,dz\rangle.
\]

A 2‑plane \(L\subset\mathbb R^4\) is **Lagrangian** if \(\omega|_L\equiv0\). We use the Euclidean inner product \(\langle\cdot,\cdot\rangle\) and norm \(|\cdot|\). All signs below are consistent with this \(J\) and \(\omega\).

## Convex bodies and polytopes

**Support / gauge / polar.**

/// admonition | Definition (Support, gauge, polar)
    type: definition
    attrs: { name: "def-support-gauge-polar" }
For a convex body \(K\subset\mathbb R^4\) with \(0\in\mathrm{int}\,K\), the support, gauge, and polar are

\[
h_K(v)=\sup_{x\in K}\langle x,v\rangle,\qquad
g_K(v)=\inf\{r>0: v\in rK\},\qquad
K^\circ = \{y: h_K(y)\le1\}.
\]
///

Gauge and support are Legendre–Fenchel dual up to the quadratic factor (Section “Clarke duality”).

**Facets and heights.** An irredundant \(H\)-representation is

\[
K = \bigcap_{i=1}^F \{x: \langle x,n_i\rangle \le h_i\},\qquad |n_i|=1,\ h_i=h_K(n_i)>0.
\]

A 3‑face is a facet \(F_i\); a 2‑face is the intersection of two or more facets.

/// admonition | Definition (Admissible polytope)
    type: definition
    attrs: { name: "def-admissible-polytope" }
A polytope \(K\subset\mathbb R^4\) is **admissible** if it is convex, bounded, full dimensional, and \(0\in\mathrm{int}\,K\). Translating the polytope can always enforce this without loss.
///

/// admonition | Definition (Lagrangian vs. non‑Lagrangian 2‑face)
    type: definition
    attrs: { name: "def-lagrangian-face" }
For a 2‑face \(G=F_i\cap F_j\) with tangent plane \(T G = \{v: \langle v,n_i\rangle=\langle v,n_j\rangle=0\}\):

- \(G\) is **Lagrangian** if \(\omega|_{TG}=0\), equivalently \(\omega(n_i,n_j)=0\).
- Otherwise \(G\) is **non‑Lagrangian**. This dichotomy governs whether facet velocities can be tangent along \(G\).
///

/// admonition | Definition (Facet velocity)
    type: definition
    attrs: { name: "def-facet-velocity" }
For each facet \(F_i\) with outward unit normal \(n_i\) and height \(h_i\) set

\[
p_i := \frac{2}{h_i}\,J n_i.
\]

These are the Hamiltonian velocities of the quadratic Hamiltonian \(H=g_K^2\) on \(\partial K\).
///

## Generalized closed characteristics on polytopes

### Normal cones and Hamiltonian inclusion
For \(x\in\partial K\) the outward normal cone is \(N_K(x)=\mathbb R_{\ge0}\,\mathrm{conv}\{n_i: x\in F_i\}\). The Hamiltonian \(H=g_K^2\) satisfies \(\partial H(x)=2\,g_K(x)\,\partial g_K(x)\) and on \(\partial K\) (where \(g_K=1\)) we have

\[
\dot\gamma(t) \in J\,N_K(\gamma(t)) = \mathrm{conv}\{p_i : \gamma(t)\in F_i\}\qquad\text{a.e.}
\]

/// admonition | Definition (Hamiltonian closed characteristic)
    type: definition
    attrs: { name: "def-closed-characteristic" }
A **(generalized) Hamiltonian closed characteristic** on \(\partial K\) is a loop \(\gamma\in W^{1,2}([0,T],\partial K)\) with period \(T>0\) such that \(\gamma(0)=\gamma(T)\) and the Hamiltonian inclusion above holds a.e. We regard two parametrized loops as the same orbit when they differ by an orientation‑preserving \(C^1\) reparametrization \(\phi:[0,T']\to[0,T]\) with \(\phi(0)=0\), \(\phi(T')=T\). This coincides with Reeb orbits on smooth approximations of \(K\) [@ArtsteinAvidanOstrover2014].
///

/// admonition | Proposition (Facet behaviour)
    type: proposition
    attrs: { name: "prop-facet-behaviour" }
Let \(K\) be an admissible polytope.

1. **Facet interior.** If \(\gamma(t)\) lies in the relative interior of \(F_i\), then \(\dot\gamma(t)=p_i\) a.e.
2. **Non‑Lagrangian 2‑face.** If \(G=F_i\cap F_j\) with \(\omega(n_i,n_j)\neq0\), no nonzero admissible velocity is tangent to \(G\); a characteristic must cross \(G\) from one adjacent facet to the other.
3. **Lagrangian 2‑face.** If \(\omega(n_i,n_j)=0\), any convex combination of \(p_i,p_j\) is tangent to \(G\), so a characteristic may slide inside \(G\).
///

/// details | Proof
    type: proof
    open: true
1. On the interior of \(F_i\), \(N_K(x)=\mathbb R_{\ge0} n_i\); the Hamiltonian inclusion gives \(\dot\gamma=c\,J n_i\). For \(H=g_K^2\) the coefficient is \(2/h_i\), hence \(\dot\gamma=p_i\).

2. On \(G\) any admissible velocity has the form \(v=a p_i+b p_j\), \(a,b\ge0\). Tangency requires \(\langle v,n_i\rangle=\langle v,n_j\rangle=0\), i.e.

    \[
    \tfrac{2b}{h_j}\,\omega(n_j,n_i)=0,\qquad
    \tfrac{2a}{h_i}\,\omega(n_i,n_j)=0.
    \]

    Since \(\omega(n_i,n_j)=-\omega(n_j,n_i)\neq0\), both equalities force \(a=b=0\), so only the zero velocity is tangent.

3. When \(\omega(n_i,n_j)=0\), the tangent plane is Lagrangian and contains \(J n_i\) and \(J n_j\); any convex combination remains tangent.
///

### Simple Hamiltonian orbits
We often work with polygonal representatives of an orbit.

/// admonition | Definition (Polygonal Hamiltonian orbit)
    type: definition
    attrs: { name: "def-polygonal-orbit" }
A Hamiltonian closed characteristic on a polytope is **polygonal** if it has a representative \(\gamma\) with a finite partition \(0=t_0<\dots<t_m=T\) such that

- each open segment \(\gamma((t_{k-1},t_k))\) lies in the relative interior of a facet \(F_{i_k}\) and is affine with constant velocity \(p_{i_k}\);
- breakpoints \(\gamma(t_k)\) lie in codimension \(\ge2\) faces; at a non‑Lagrangian 2‑face \(F_{i_k}\cap F_{i_{k+1}}\) the path crosses directly from \(F_{i_k}\) to \(F_{i_{k+1}}\); at a Lagrangian 2‑face we may insert a (short) tangent subsegment with velocity in \(\mathrm{conv}\{p_{i_k},p_{i_{k+1}}\}\).
///

/// admonition | Definition (Simple Hamiltonian orbit)
    type: definition
    attrs: { name: "def-simple-orbit" }
A simple Hamiltonian orbit is a polygonal orbit that visits each facet at most once. Fix the representative whose total time is \(1\) and write \(s_i>0\) for the time spent with velocity \(p_i\) on facet \(F_i\). Set \(\beta_i := s_i/h_i\); then \(\sum_i \beta_i h_i = \sum_i s_i = 1\) and the closing condition \(\sum_i s_i p_i = 0\) becomes \(\sum_i \beta_i n_i = 0\). Thus the orbit is encoded by a cyclic permutation \(\sigma\) of the visited facets and positive coefficients \(\beta_i\); the affine segments have lengths \(h_i\beta_i\) in time and are traversed with velocity \(p_i\).
///

HK2017 prove an action minimizer admits a simple representative; CH2021 refine rotation bounds for non‑Lagrangian polytopes [@HK2017; @CH2021].

*Lean formalization note.* Encode a simple orbit by the cyclic order \(\sigma\) of facets visited and positive coefficients \(\beta_i\) satisfying \(\sum_i \beta_i h_i = 1\) and \(\sum_i \beta_i n_i = 0\); the segment on \(F_i\) then has duration \(h_i\beta_i\) and velocity \(p_i\). Reparametrization invariance is absorbed by the normalization \(\sum_i \beta_i h_i = 1\).

## Action and the EHZ capacity

/// admonition | Definition (Action)
    type: definition
    attrs: { name: "def-action" }
For a loop \(\gamma:[0,T]\to\mathbb R^4\),

\[
A(\gamma)=\tfrac12\int_0^T \langle J\gamma(t),\dot\gamma(t)\rangle\,dt = \int_0^T \lambda(\dot\gamma(t))\,dt.
\]
///

Reversing orientation changes the sign of \(A\); we minimize over positive-action parametrizations. On a contact-type hypersurface the action equals the period.

/// admonition | Definition (Ekeland–Hofer–Zehnder capacity)
    type: definition
    attrs: { name: "def-ehz-capacity" }
For a convex body \(K\),

\[
 c_{\mathrm{EHZ}}(K)=\min\{A(\gamma): \gamma \text{ closed characteristic on }\partial K\}.
\]
///

For smooth convex \(K\) this equals both the first Ekeland–Hofer and Hofer–Zehnder capacities; continuity extends the definition to all convex bodies [@EkelandHofer1990; @HoferZehnder1990; @ArtsteinAvidanOstrover2014]. Fundamental properties: monotonicity under inclusion, 2‑homogeneity under scaling, translation invariance, and \(c_{\mathrm{EHZ}}(B(r))=c_{\mathrm{EHZ}}(Z(r))=\pi r^2\).

We use the systolic ratio.

/// admonition | Definition (Systolic ratio)
    type: definition
    attrs: { name: "def-systolic-ratio" }
For a convex body \(K\subset\mathbb R^4\), the systolic ratio is

\[
\operatorname{sys}(K)=\frac{c_{\mathrm{EHZ}}(K)^2}{2\,\operatorname{vol}(K)}.
\]
///

## Gauge–support duality and Clarke’s functional

Fenchel duality yields

\[
 g_K(x)^2 = \sup_y \big( \langle x,y\rangle - \tfrac14 h_K(y)^2 \big),\qquad
 \tfrac14 h_K(y)^2 = \sup_x \big( \langle x,y\rangle - g_K(x)^2 \big),
\]

with equality iff \(y\in\partial g_K^2(x)\) iff \(x\in\partial(\tfrac14 h_K^2)(y)\). This identifies supporting facets and contact points via Legendre duality.

Clarke’s dual action principle (specialized to convex bodies) considers

\[
E = \Big\{ z\in W^{1,2}([0,1],\mathbb R^4): \int_0^1 \dot z = 0,\ \int_0^1 \langle -J\dot z,z\rangle dt = 1 \Big\},
\qquad
I_K(z)=\tfrac14\int_0^1 h_K^2(-J\dot z(t))\,dt.
\]

Critical points of \(I_K\) correspond to generalized characteristics, and

\[
 c_{\mathrm{EHZ}}(K) = \inf_{z\in E} I_K(z).
\]

For polytopes \(h_K\) is piecewise linear, so \(I_K\) is piecewise quadratic in \(\dot z\); minimizers can be taken piecewise affine, leading to the combinatorial model below [@HK2017].

## HK/CH combinatorial capacity formula (4D)

Let \((n_i,h_i)_{i=1}^F\) be the outward unit normals and heights of an admissible polytope \(K\subset\mathbb R^4\). Define coefficients \(\beta_i\ge0\) with

\[
\sum_i \beta_i h_i = 1,\qquad \sum_i \beta_i n_i = 0.
\]

For a permutation \(\sigma\in S_F\), set

\[
Q(\sigma,\beta)=\sum_{j<i} \beta_{\sigma(i)}\,\beta_{\sigma(j)}\,\omega(n_{\sigma(i)},n_{\sigma(j)}).
\]

/// admonition | Theorem (HK combinatorial formula, 4D)
    type: theorem
    attrs: { name: "thm-hk-combinatorial" }
Haim‑Kislev’s formula gives

\[
c_{\mathrm{EHZ}}(K) = \frac{1}{2}\Big[\max_{\sigma,\beta} Q(\sigma,\beta)\Big]^{-1}.
\]

In the centrally symmetric case the factor becomes \(\tfrac14\) with paired normals. The maximizer encodes a simple action‑minimizing orbit: velocities appear in the order \(\sigma\) with normalized time weights \(\beta_{\sigma(i)}\) as in the definition of simple orbits. Chaidez–Hutchings show that for non‑Lagrangian polytopes any minimizer has combinatorial rotation number \(\rho\le2\), giving a finite search set for algorithms [@CH2021].
///

## Forward use
This chapter fixes conventions and the variational/combinatorial tools used in later chapters. The forthcoming Chapter 02.1 will work out the HK2024 counterexample and other explicit polytopes using these conventions. Algorithms and Lean formalisations will cite the definitions, facet dynamics, duality, and the HK/CH formula established here.
