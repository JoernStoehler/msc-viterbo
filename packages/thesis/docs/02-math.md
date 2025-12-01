
# Math Background

This chapter sets notation and definitions for the rest of the thesis. We follow primarily @ChaidezHutchings2021 and secondarily @HaimKislev2017, @HaimKislev2024 in our choice of notation.  
We assume the reader is already familiar with basic symplectic geometry in a smooth setting, as per a master's level course (Reeb vector fields, contact forms, symplectic capacities, Hamiltonian dynamics).

## Standard Symplectic \(\mathbb{R}^4\)

We work in the standard \(\mathbb R^4\) setting:

Coordinates

:   \(z=(q_1,q_2,p_1,p_2)\)

Inner product

:   \(\langle x,y\rangle = x^T y\)

Norm

:   \(|x|=\sqrt{\langle x,x\rangle}\)

Volume form

:   \(\mathrm{vol} = \prod_{i=1}^2 dq_i \wedge dp_i\)

Almost complex structure

:   \(J = \begin{pmatrix}0 & -I_2 \\ I_2 & 0\end{pmatrix} ,\quad J^2 = -I_4\)

Symplectic form

:   \(\omega = \sum_{i=1}^2 dq_i \wedge dp_i ,\quad \omega(x,y)=\langle Jx,y\rangle\)

Liouville 1‑form

:   \(\lambda = \tfrac12 \sum_{i=1}^2 (q_i\,dp_i - p_i\,dq_i) ,\quad \lambda_z(\dot z) = \tfrac12 \langle J z, \dot z\rangle ,\quad d\lambda = \omega\)

Lagrangian 2-plane

:   An affine 2-plane \(L\subset\mathbb R^4\) is Lagrangian iff \(\omega|_L \equiv 0\).

## Convex Bodies and Polytopes


Half-space

:   For \(n\in\mathbb R^4\), \(|n|=1\), and \(h \in \mathbb R\), the half-space \(\{x: \langle x,n\rangle \le h\}\) has a boundary hyperplane \(\{x: \langle x,n\rangle = h\}\) and outward unit normal \(n\). Iff \(h>0\) the half-space contains \(0\) in its interior, and we call it positive.

Admissable, aka Bounded Convex Star-Shaped

:   A set \(K\subset\mathbb R^4\) is called bounded, convex in the usual sense, and star-shaped iff it contains \(0\) in its interior. Due to convexity, every ray from \(0\) through a boundary point cuts the boundary transversely and exactly once. Any star-shaped body is full-dimensional since it contains a neighborhood of \(0\). We abbreviate "bounded convex star-shaped body" as "admissable body". Any bounded convex body with non-empty interior can be translated to an admissable body.

Irredundant H-representation

:   Any admissable polytope \(K\) has a unique representation as the intersection of finitely many positive half-spaces, with minimal number of half-spaces. Writing the outward unit normals and heights as \((n_i,h_i)_{i=1}^F\), \(|n_i|=1\), \(h_i>0\), we have \(K = \bigcap_{i=1}^F \{x: \langle x,n_i\rangle \le h_i\}\). Any such representation with bounded \(K\) defines an admissable polytope.

Boundary of a Convex Body

:   We write \(\partial K\) for the boundary of a convex body \(K\subset\mathbb R^4\).

Facets and Faces

:   For an admissable polytope \(K\) the boundary decomposes into finitely many facets (aka 3-faces) \(F_i = K \cap \{x: \langle x,n_i\rangle = h_i\}\). We take our facets to be closed sets relative to the hyperplane topology. Where multiple hyperplanes meet, we have lower-dimensional 2-, 1-, and 0-faces. It's important to note that due to irredundancy, every 2-face is the intersection of two unique facets. For 1-faces and 0-faces, unboundedly many facets may meet. We call the \(n_i, h_i\) the facet normals and heights.



Support

:   For an admissable body \(K\subset\mathbb R^4\) the support function is \(h_K(v) = \max_{x\in K} \langle x,v\rangle\). For polytopes, for any facet \(F_i\) we have \(h_K(n_i) = h_i\).

Gauge

:   For an admissable body \(K\subset\mathbb R^4\) the gauge function is \(g_K(v) = \min\{r>0: v\in rK\}\). On the boundary \(x \in \partial K\) we have \(g_K(x)=1\).

Polar

:   For an admissable body \(K\subset\mathbb R^4\) the polar body is \(K^\circ = \{y: h_K(y) \le 1\}\). For admissable polytopes, the polar is again an admissable polytope with vertices at the points \(n_i/h_i\) for every facet \(F_i\) of \(K\).

## Correspondence of Combinatorial and Smooth Settings

The reason we are interested in admissable polytopes is that they approximate any bounded convex star-shaped body arbitrarily well in the Hausdorff metric, and other metrics of interest. Understanding the polytope case is a key step towards understanding general convex bodies.

We will in several places make statements that the "combinatorial" definition of some symplectic data on polytopes is indeed the limit of the symplectic data for smoothings of the polytope, which are \(C^{1}\) admissable bodies.


\(\varepsilon\)-Smoothings

:   For an admissable polytope \(K\) and \(\varepsilon>0\), the \(\varepsilon\)-smoothing \(K_\varepsilon := \{x \in \mathbb R^4 : \mathrm{dist}(x,K) \le \varepsilon\}\) is an admissable body with \(C^{1,1}\) boundary. Any sequence of admissable bodies that converges to \(K\) in the Hausdorff metric is contained in a sequence of \(\varepsilon\)-smoothings with \(\varepsilon \to 0\).

## Hamiltonian Dynamics

Standard Hamiltonian

:   For our interests any choice of Hamiltonian \(H: \mathbb R^4 \to \mathbb R\) with regular level set \(H^{-1}(1) = \partial K\) and some sufficient regularity will do. We fix a standard Hamiltonian that will later be useful for computations and for applying a Clarke dual principle. We set \(H = g_K^2\), the square of the gauge function of \(K\). This is 2-homogeneous, convex, and piecewise quadratic for polytopes. Derivatives exist everywhere except on the rays through the \(2\)-faces of \(K\).

Hamiltonian vector field (Regular case)

:   For \(H \in C^1(\mathbb R^4)\) the Hamiltonian vector field \(X_H \in \Gamma^0(T\mathbb R^4)\) is defined by \(\omega(X_H,\cdot) = dH(\cdot)\), or equivalently \(X_H = J \nabla H\).

Hamiltonian flow, trajectories (Regular case)

:   We can define a flow \(\phi_H^t: \mathbb R^4 \to \mathbb R^4\) generated by \(X_H\) via the ODE \(\dot x(t) = X_H(x(t))\). The trajectories \(x(t) = \phi_H^t(x_0)\) with initial condition \(x(0)=x_0\) exist and, for some conditions on \(H\) we don't discuss here, are unique for all time. The flow preserves level sets of \(H\), so in particular \(\partial K\) is invariant under the flow.

Combinatorial Hamiltonian dynamics (Polytope case)

:   For admissable polytopes \(K\) the Hamiltonian \(H=g_K^2\) is not differentiable everywhere, so the standard Hamiltonian vector field and flow are not defined globally. Instead we work with generalized Hamiltonian dynamics via differential inclusions, as in @HaimKislev2017. We use the subdifferential \(\partial H(x)\) in place of the gradient \(\nabla H(x)\) to define a Hamiltonian inclusion \(\dot x(t) \in J \partial H(x(t)) \, \text{a.e.}\). Solutions in \(W^{1,2}(\mathbb R, \mathbb R^4)\) exist for any initial condition and all time, but need not be unique. We still have that \(\partial K\) is invariant under the generalized flow, i.e. any solution with initial condition in \(\partial K\) remains in \(\partial K\) for all time.

Combinatorial Hamiltonian orbits (Polytope case)

:   We call a periodic solution \(\gamma \in W^{1,2}(\mathbb T, \partial K)\) of the Hamiltonian inclusion a Hamiltonian orbit, where \(\mathbb T = \mathbb R / T \mathbb Z\) for some minimal period \(T>0\). Not all solutions need be periodic. We exclude stationary solutions \(\gamma \equiv \text{const}\) by the \(T > 0\) requirement, since they will not be interesting for us later on.

Subdifferential

:   For a convex function \(f: \mathbb R^n \to \mathbb R\) the subdifferential at \(x\) is the set of subgradients \(\partial f(x) = \{v \in \mathbb R^n : f(y) \ge f(x) + \langle v, y - x \rangle \text{ for all } y \in \mathbb R^n\}\). So \(\partial f(x)\) is the set of slopes of affine functions that globally underestimate \(f\) and touch \(f\) at \(x\). If \(f\) is differentiable at \(x\), then \(\partial f(x) = \{\nabla f(x)\}\).

Subdifferential of \(H = g_K^2\)

:   At any \(x \in \partial K\) for an admissable polytope \(K\) we have subgradients for every facet \(F_i\) containing \(x\). In fact, we can easily see that the underestimating affine functions are the half-spaces containing \(K\), and their slopes are the convex combinations of the facet normals at \(x\). Thus \(\partial H(x) = 2 g_K(x) \, \partial g_K(x) = \mathrm{conv}\{(2/h_i) \, n_i : x \in F_i\}\).

Facet velocities

:   We define the facet velocities \(p_i = (2/h_i) \, J n_i\) for each facet \(F_i\) of an admissable polytope \(K\). The Hamiltonian inclusion on \(\partial K\) can then be written as \(\dot x(t) \in \mathrm{conv}\{p_i : x(t) \in F_i\} \, \text{a.e.}\). And in the interior of a facet \(F_i\) we have the unique velocity \(\dot x(t) = p_i\).

## Reeb Dynamics and Closed Characteristics

Contact form and Reeb vector field (Regular case)

:   Let \(\partial K\) be a \(C^1\) boundary of an admissable body. It is a contact-type hypersurface with contact form \(\alpha = \lambda|_{\partial K}\). The Reeb vector field defined by \(\alpha(R) = 1\), \(d\alpha(R,\cdot) = 0\) can be explicitly given. For a point \(x \in \partial K\), with outwards unit normal \(n_x \in \mathbb R^4\), \(|n_x| = 1\), we have that any direction \(v \in T_x \partial K\) satisfies \(\langle J v, J n_x \rangle = \langle v, n_x \rangle = 0\). Thus \(J n_x \in \mathrm{ker}(d\alpha_x)\). Normalizing to \(\alpha(R) = 1\) gives \(R(x) = (2 / \langle x, n_x \rangle) \, J n_x\).

Reeb flow and Reeb orbits (Regular case)

:   Just like in the Hamiltonian case, we can define a flow and ODE, this time only on \(\partial K\), via \(\dot x(t) = R(x(t))\). The flow preserves \(\alpha\) and \(d\alpha\). Periodic solutions are called Reeb orbits.

Closed characteristics (Regular case)

:   If we relax the ODE and only demand that some loop \(\gamma: S^1 \to \partial K\) have its tangent vector \(\dot\gamma(t)\) be parallel with same orientation to the Reeb vector field, i.e. \(\dot\gamma(t) \in \mathrm{ker}(d\alpha_{\gamma(t)}) \land \alpha(\dot\gamma(t)) > 0\) for all \(t\), we call such loops closed characteristics. On admissable bodies with enough regularity, closed characteristics coincide with Reeb orbits up to orientation-preserving reparametrization. We can also turn the Reeb flow for some contact form (\alpha\) into a Hamiltonian flow near \(\partial K\) and vice versa, with some caveats on regularity, so basically closed characteristics and Reeb orbits and Hamiltonian orbits on \(\partial K\) all give us the same geometric information.

Reeb orbits, Closed characteristics, Hamiltonian orbits (Polytope case)

:   For admissable polytopes \(K\) we instantly spot that on the interior of facets the (well-defined) Reeb vector field equals the Hamiltonian velocity. So the generalized Reeb orbits for the standard contact form are just the generalized Hamiltonian orbits on \(\partial K\) for our choice of Hamiltonian \(H = g_K^2\). The generalized closed characteristics are then defined as the loops \(\gamma \in W^{1,2}(S^1, \partial K)\) whose tangent vectors satisfy the inclusion \(\dot\gamma(t) \in \mathrm{cone}\{p_i : \gamma(t) \in F_i\}\, \text{a.e.}\). Note that the cone for us here only contains combinations with nonnegative and not-all-zero coefficients. We again basically have equivalence of the three notions of orbits, up to orientation-preserving reparametrizations.

## Action, EHZ Capacity, and Systolic Ratio

The notion of closed characteristics allows us to define a symplectic capacity \(c_{\mathrm{EHZ}}\) on admissable bodies with enough regularity. Since we already defined generalized closed characteristics on polytopes, we can define \(c_{\mathrm{EHZ}}\) there as well. By continuity of all symplectic capacities with respect to the Hausdorff metric, it's easy to see that the capacity defined on polytopes coincides with the limit of the capacities of their smoothings.

Action

:   For a curve \(\gamma\) in \(\mathbb R^4\), the action is defined as \(A(\gamma) = \int_\gamma \lambda = \int_0^T \lambda_{\gamma(t)}(\dot\gamma(t))\,dt = \tfrac12 \int_0^T \langle J \gamma(t), \dot\gamma(t) \rangle\, dt\). This definition is independent of the choice of orientation-preserving reparametrization, and the action changes sign if we reverse orientation. This definition works for \(W^{1,2}\) curves already.

EHZ Capacity

:   For an admissable body \(K\) with enough regularity, there is a closed characteristic \(\gamma\) on \(\partial K\) that minimizes the action among all closed characteristics. The minimum action, which equals the Ekeland–Hofer-Zehnder capacity \(c_{\mathrm{EHZ}}(K) = \min\{A(\gamma) : \gamma \text{ closed characteristic on } \partial K\}\), defines a symplectic capacity. In the polytope case we use the same definition with generalized closed characteristics.

Systolic Ratio

:   The systolic ratio \(\mathrm{sys}(K) = c_{\mathrm{EHZ}}(K)^2 / (2 \, \mathrm{vol}(K))\) is a dimensionless quantity. It is scale invariant and translation invariant. The systolic ratio of the ball and cylinder of radius \(r\) is \(\mathrm{sys}(B(r)) = \mathrm{sys}(Z(r)) = 1\).


## Viterbo Conjecture (falsified)

We can now finally state the famous Viterbo's conjecture, which was long believed by many to be true, but has recently been falsified by @HaimKislev2024.

/// admonition | Conjecture (Viterbo's conjecture)
    type: conjecture
    attrs: { name: "conj-viterbo" }
For any admissable body \(K \subset \mathbb R^4\), the systolic ratio satisfies \(\mathrm{sys}(K) \le 1\).
///

/// admonition | Counterexample (Viterbo's conjecture)
    type: example
    attrs: { name: "ex-counterexample-viterbo" }
From @HaimKislev2024, there exists an admissable polytope \(K \subset \mathbb R^4\) with \(\mathrm{sys}(K) > 1\), thus falsifying Viterbo's conjecture.
///

Goal of this master's thesis is to probe the landscape of admissable polytopes further, to find more counterexamples, and conjecture or even prove mathematically interesting statements about when Viterbo's conjecture does or does not hold.

The existing literature already covers a few interesting statements:

/// admonition | Theorem (Master Thesis Haim-Kislev)
    type: theorem
    attrs: { name: "thm-simplex-viterbo" }
For simplices, which if they are star-shaped are automatically admissable polytopes, Viterbo's conjecture holds with an even stronger bound: \(\mathrm{sys}(K) \le 3/4 < 1\). Equality is taken only for the orthonormal simplex with vertices \(\{0, e_1, e_2, e_3, e_4\}\) and its symplectomorphic images, i.e. translations and linear symplectic maps.
///

/// admonition | Theorem (Mahler-Conjecture in 2D)
    type: theorem
    attrs: { name: "thm-mahler-2d-viterbo" }
The Mahler Conjecture in 2D is known to hold: for any centrally symmetric convex polygon \(P = - P \subset \mathbb R^2\) we have \(\mathrm{area}(P) \, \mathrm{area}(P^\circ) \ge 8\), with equality for parallelograms. It turns out that the Mahler conjecture is equivalent to Viterbo's conjecture for \(K = P \times P^\circ \subset \mathbb R^4\), where \(P^\circ\) is the polar of \(P\), and equality is preserved. Thus Viterbo's conjecture holds for such \(K\).
///

We can trivially construct a family of counterexamples to Viterbo's conjecture by using the 2024 counterexample as base and applying scalings, symplectomorphisms, and by doing small continuous deformations. Since the systolic ratio is continuous in the Hausdorff metric, small perturbations of a counterexample remain counterexamples.

We are interested in finding more counterexamples that are not trivially derived from the known one. For that, we need a way to probe different polytopes systematically, and computationally, rather than calculating the systolic ratio by hand, using ad-hoc methods, for hand-picked polytopes.

The first major result of this thesis is to develop such a computational method that is applicable to all admissable polytopes, and is performant enough to be used for data science and machine learning methods that require large datasets of polytopes and their symplectic data.

Before we dive into discussing the computational methods, we need to discuss the behavior of the Reeb orbits (or Hamiltonian orbits) on polytopes in more detail.

## Behavior of Reeb Orbits on Polytopes

Fix now an admissable polytope \(K \subset \mathbb R^4\) with irredundant H-representation via facet normals and heights \((n_i, h_i)_{i=1}^F\), \(|n_i| = 1\), \(h_i > 0\).
Recall the facet velocities \(p_i = (2/h_i) \, J n_i\).

The main result we want to recall from the previous sections is that

/// admonition | Fact
    type: theorem
Any closed characteristic \(\gamma\) corresponds to a Reeb orbit, which also is a Hamiltonian orbit for the Hamiltonian \(H = g_K^2\). It is parametrized uniquely then as \(\gamma \in W^{1,2}(\mathbb T, \partial K)\) with period \(T > 0\) such that 
\(
\dot\gamma(t) \in \mathrm{conv}\{p_i : \gamma(t) \in F_i\} \, \text{a.e.}
\)
///

In the interior of a facet \(F_i\) the velocity is constant \(\dot\gamma(t) = p_i\), and so the orbit has a linear segment there. 

/// admonition | Lemma (Flow on Facets)
    type: lemma
    attrs: { name: "lem-facet-flow" }
If the orbit \(\gamma\) touches the interior of a facet \(F_i\), then it does so as part of a closed linear segment with velocity \(p_i\), which starts and ends at the boundary of \(F_i\) after finite time, i.e. at a 2-face, 1-face, or 0-face.
///
/// details | Proof
    type: proof
    open: true
Trivial.
///

At the intersections of facets, i.e. at lower-dimensional faces, we have more complicated behavior.

If the orbit \(\gamma\) touches a (closed, non-empty) 2-face \(F_{ij} = F_i \cap F_j\), we have two cases to consider: either the 2-face is Lagrangian, i.e. lies in a Lagrangian plane, or it is non-Lagrangian.

/// admonition | Lemma (Flow on Lagrangian 2-Faces)
    type: lemma
    attrs: { name: "lem-lagrangian-2face" }
If \(F_{ij}\) is Lagrangian, then both facet velocities \(p_i\) and \(p_j\) lie in the tangent plane of \(F_{ij}\). Locally, the Reeb orbit may a-priori slide along \(F_{ij}\) with any \(W^{1,2}\) velocity in \(\mathrm{conv}\{p_i, p_j\}\), and need not be piecewise linear. The orbit enters and exits \(F_{ij}\) after finite time in its boundary, i.e. in a 1-face or 0-face.
///

/// details | Proof
    type: proof
    open: true
The basic idea is that since \(p_i, p_j\) both are parallel to \(F_{ij}\), the Reeb orbit cannot enter from the interior of the 3-faces into the interior of the 2-face. It must pass through the boundary instead. Also \(0 \notin \mathrm{conv}\{p_i, p_j\}\), so the 1-form \(\alpha\) is constant and non-zero along the 2-face, integrates to a potential on the 2-face, and thus the orbit cannot stay in the 2-face forever.
///

/// admonition | Lemma (Flow through Non-Lagrangian 2-Faces)
    type: lemma
    attrs: { name: "lem-nonlagrangian-2face" }
If \(F_{ij}\) is non-Lagrangian, then there's a direction \(i \to j\) or \(j \to i\) such that the Reeb orbit touches the interior of \(F_{ij}\) only at isolated times, crossing directly from one facet to the other along the position-independent direction. The direction is determined by the sign of \(\omega(n_i, n_j)\): if \(\omega(n_i, n_j) > 0\), then the orbit crosses from \(F_i\) to \(F_j\); if \(\omega(n_i, n_j) < 0\), then it crosses from \(F_j\) to \(F_i\).
///
/// details | Proof
    type: proof
    open: true
Key idea is that \(\langle J n_i, n_j \rangle = - \langle J n_j, n_i \rangle = \omega(n_i, n_j)\). The value is zero iff the 2-face is Lagrangian. The inner product tells us whether \(p_i\) points into or out of the half-space defined by \(F_j\), and thus into or out of \(K\) and the facet \(F_i\).
Locally, around an interior point of \(F_{ij}\), the orbit consists of two linear segments, one in \(F_i\) with velocity \(p_i\) and one in \(F_j\) with velocity \(p_j\). So we get that the touching time is isolated, and the crossing direction is as claimed.
///

For 1-faces, there is a unique direction, but not necessarily a unique velocity.

/// admonition | Lemma (Flow on 1-Faces)
    type: lemma
    attrs: { name: "lem-1face-flow" }
If the orbit \(\gamma\) touches the interior of a 1-face \(F = \bigcap_{k=1}^m F_{i_k}\), which is an intersection of \(m \ge 3\) facets, then there is a unique direction along which the orbit may flow along \(F\). There is a-priori no additional statement we can make about the velocity, and the orbit may enter and exit \(F\) both in the boundary 0-faces and interior points of \(F\). So we don't know much, only that the orbit enters and exits through an adjacent 0-face, or through the interior of an adjacent 2- or 3-face.
///

/// details | Proof
    type: proof
    open: true
Key idea is to use the convexity of \(K\) to view the local neighborhood as an intersection of half-spaces. This implies the normals don't convexly combine to zero, as then the intersection would be empty. Thus the velocities \(p_{i_k}\) also don't convexly combine to zero, and there is a unique half-line the convex span lies in. This gives the unique direction of flow along the 1-face.
If we look at trajectories instead of orbits, then we can indeed give examples of polytopes where trajectories enter and exit 1-faces in all the fashions described.
///

/// admonition | Lemma (Flow on 0-Faces)
    type: lemma
    attrs: { name: "lem-0face-flow" }
Nothing to be said about 0-faces.
///

### Generic Behavior

One potentially interesting question is what of the above behavior is just an edge case, i.e. whether there's some generic property that simplifies the behavior of closed characteristics on polytopes.

/// admonition | Lemma (Non-Lagrangianness is Generic)
    type: lemma
    attrs: { name: "lem-nonlagrangian-generic" }
The set of admissable polytopes with at no Lagrangian 2-faces is "open" and "dense" in some reasonable sense.
///
/// details | Proof
    type: proof
    open: true
For a fixed number of vertices, or fixed number of facets, the set of admissable polytopes can be viewed as an open subset of \(\mathbb R^{4F}\) or \(\mathbb R^{4V}\) respectively, parametrized by the facet normals and heights or vertex coordinates respectively. The Lagrangianness of a 2-face defined by facets \(F_i, F_j\) is a single equation \(\omega(n_i, n_j) = 0\), which defines a codimension 1 submanifold. Thus the set of polytopes with at least one Lagrangian 2-face is a finite union of such codimension 1 submanifolds, and its complement, the set of polytopes with no Lagrangian 2-faces, is open and dense.
///

/// admonition | Conjecture
    type: conjecture
    attrs: { name: "conj-generic-0-faces" }
For a "generic" admissable polytope, no closed characteristic passes through a 0-face.
///
/// details | Note
    type: note
    open: true
This conjecture was voiced by @ChaidezHutchings2021. Quote:
> "We expect that Type 2 combinatorial Reeb orbits do not exist for generic polytopes; see Conjecture 1.26 below." (p.7)
///

Besides asking about generic properties, we can also try to classify degeneracies. In particular, we care about degeneracies of multiple closed characteristics having the same action, since that also may complicate finding the minimal action, depending on our algorithmic approach.

### Degeneracies of the Action

/// admonition | Definition (Polygonal Orbit)
    type: definition
    attrs: { name: "def-piecewise-constant-velocity" }
A Reeb/Hamiltonian orbit is **polygonal** if we can partition time into finitely many open intervals, such that during each interval the orbit does not change what facets it lies on, and has constant velocity equal to one of the incident facet velocities \(p_i\). Note that the velocity is no longer a convex combination. Note that we don't require the orbit to lie only on 3-faces, or intervals to correspond to changes in the incident facet set. Breakpoints may occur anywhere.
///

/// admonition | Theorem (Homotopy to Polygonal Orbit)
    type: theorem
    attrs: { name: "thm-homotopy-pl" }
Any Hamiltonian/Reeb orbit \(\gamma\) is homotopic through Hamiltonian/Reeb orbits of the same action to a polygonal orbit \(\gamma'\).
///
/// details | Proof
    type: proof
    open: true
There is a proof in @HaimKislev2017 using Clarke's dual principle. Here we use our previous observations about the flow on facets and faces to give a more geometric proof. 

Let \(\gamma\) be a Hamiltonian/Reeb orbit with period \(T>0\). 

First we consider the map from time into the face lattice of \(K\), sending \(t\) to the minimal face containing \(\gamma(t)\). We previously discussed all the ways an orbit can change faces, and know that it happens on isolated times only. By compactness, we get a finite partition into open intervals, where we drop faces that are crossed instantaneously through their interior, e.g. non-Lagrangian 2-faces, 0-faces, and perhaps some 1-faces, but never Lagrangian 2-faces or 3-faces.

In the case of 3-faces, the velocity is already constant.

In remains to consider the case of Lagrangian 2-faces and of 1-faces with positive length intervals.

For the Lagrangian 2-face, the two facet velocities \(p_i, p_j\) form a basis(quick check from convexity of the polytope). 
We restrict to the interval, and split \(\dot\gamma(t) = a(t) p_i + b(t) p_j\) and integrate to get total contributions \(A = \int a(t) dt\), \(B = \int b(t) dt\).
We can homotope \(\gamma\) using mixtures that leave \(A,B\) constant, to a path where \(a(t) = 1_{[0,A]}(t)\), \(b(t) = 1_{[A,A+B]}(t)\). This gives a polygonal path segment.
The linearity of the action functional implies:
\(A(\gamma) = \int \tfrac12 \langle J \gamma(t), \dot\gamma(t) \rangle dt = + \int \tfrac12 \langle \gamma(t), a(t) J p_i + b(t) J p_j \rangle dt\).
However, since \(J p_i, J p_j\) are both perpendicular to the 2-face and any possible velocities along it, we have that \(\langle \gamma(t), J p_i \rangle = \text{const}\), and so that \(A(\gamma)\) only depends on \(\int a(t) dt\) and \(\int b(t) dt\), which we kept constant. Thus the action is preserved, and we don't even have to change the interval length.

For the 1-face case, may have convex combinations of three or more velocities. Just like before however the action functional is linear and the 1-face is perpendicular to all \(J p_i\), so we can again homotope to a polygonal path segment without changing the action.

Putting everything together, we get a homotopy of \(\gamma\) to a polygonal orbit \(\gamma'\), along Reeb/Hamiltonian orbits of the same action.
///

/// admonition | Definition (Simple Orbit)
    type: definition
    attrs: { name: "def-simple-orbit-2" }
A polygonal Hamiltonian/Reeb orbit is **simple** if every facet velocity \(p_i\) is used at most once. Note that breakpoints may still lie in the interior of 2-faces or 1-faces.
///

/// admonition | Theorem (Homotopy to Simple Orbit)
    type: theorem
    attrs: { name: "thm-min-action-simple" }
Any Hamiltonian/Reeb orbit has a homotopy through Hamiltonian/Reeb orbits to a simple orbit where the action is non-increasing along the homotopy.
///
/// details | Proof
    type: proof
    open: true
Omitted. There is a similar theorem with proof in @HaimKislev2017 that uses Clarke's dual principle. It doesn't show a homotopy, only that for any orbit there's a simple orbit with less or equal action.
///

/// admonition | Corollary (Simple Minimum Action Orbit)
    type: corollary
    attrs: { name: "cor-simple-min-action" }
There is a minimum action Hamiltonian/Reeb orbit that is simple.
///

While we have shown that any minimum action orbit is homotopic to a simple orbit, we have made no statement that all minimum action orbits are homotopic to each other.

/// admonition | Example (Viterbo Counterexample Degeneracy)
    type: example
    attrs: { name: "ex-viterbo-degeneracy" }
The counterexample to Viterbo's conjecture from @HaimKislev2024 has multiple distinct minimum action closed characteristics, which are all homotopic to each other.

See @HaimKislev2024 for details, e.g. Figure 4. The basic idea is that in the two-bounce orbits we can move one bounce point along a pentagon edge while the other stays at a vertex. Then we can switch and move the point that we previously kept still along an edge. This way all two-bounce orbits can be homotoped. Three-bounce orbits can be homotoped into a two-bounce orbit by moving two bounce points that neighbor the same vertex towards the vertex together, until they both reach the vertex at the same time.
///

## Clarke's Dual Action Principle

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
