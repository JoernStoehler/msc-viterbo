---
---

# Symplectic Geometry on Polytopes

```text
We repeat various known facts about symplectic geometry on polytopes, interpreted as the limit of symplectic geometry on smooth objects that converge to polytopes in some notion (e.g. C^0 on the boundary). We restrict ourselves to R^4, the simplest non-trivial case. We restrict ourselves further to convex polytopes, since they are interesting for the Viterbo conjecture, and for simplicity we also demand them to be star-shaped i.e. containing the origin in their interior.
```

## Basic Symplectic Geometry

- The standard symplectic form on $\mathbb{R}^4$ is given by
  $$\omega = dx_1 \wedge dy_1 + dx_2 \wedge dy_2,$$
  where we write points in $\mathbb{R}^4$ as $(x_1, y_1, x_2, y_2)$.
- The standard Liouville 1-form on $\mathbb{R}^4$ is given by
  $$\lambda = \frac{1}{2} \sum_{i=1}^2 (x_i dy_i - y_i dx_i).$$
- The standard complex structure $J$ on $\mathbb{R}^4$ is given by
  $$J = \begin{pmatrix} 0 & I \\ -I & 0 \end{pmatrix},$$
  where $I$ is the $2 \times 2$ identity matrix.
- A submanifold $L \subset \mathbb{R}^4$ is called Lagrangian if $\dim L = 2$ and $\omega|_L = 0$.
- A symplectomorphism is a diffeomorphism $\phi: \mathbb{R}^4 \to \mathbb{R}^4$ such that $\phi^* \omega = \omega$.
- We fix a convex, compact, star-shaped polytope $K \subset \mathbb{R}^4$. It's boundary $\partial K$ consists of a skeleton of 3-faces, 2-faces, 1-faces and 0-faces (vertices).
- A Hamiltonian function $H: \mathbb{R}^4 \to \mathbb{R}$ generates a Hamiltonian vector field $X_H$ defined by $\iota_{X_H} \omega = dH$. Or equivalently $X_H = J \nabla H$. While ususally we consider smooth Hamiltonians, we here are interested only in a non-smooth limit case:
  $$H(z) = g_{K}(z)^2,$$
  where $g_K$ is the gauge function of $K$, defined as
  $$g_K(z) = \inf \{ r > 0 : z \in rK \}.$$
  The Hamiltonian is convex, $C^0$ on $\mathbb{R}^4$ and smooth except on rays through the $\leq 2$-faces of $K$.
- The energy surface $H^{-1}(1) = \partial K$ is the boundary of the polytope. The sublevel set $H^{-1}((-\infty, 1]) = K$ is the polytope itself.
- We take the usual action functional on the loop space of $\mathbb{R}^4$:
  $$\mathcal{A}(\gamma) = \int_\gamma \lambda - \int_0^T H(\gamma(t)) dt,$$
  where $\gamma: [0,T] \to \mathbb{R}^4$ is a loop.
  For us it suffices to have $\gamma \in W^{1,2}([0,T], \mathbb{R}^4)$.
- In the smooth case, the critical points of $\mathcal{A}$ correspond to periodic orbits of the Hamiltonian vector field $X_H$, up to parametrization. In particular, we can restrict to critical points on the energy surface $H^{-1}(1) = \partial K$, which are the closed characteristics on $\partial K$, and which correspond up to parametrization to periodic orbits of $X_H$ with energy $1$.
- In the polytope case, we keep the notion of critical points, and can again restrict to $\gamma: [0,T] \to \partial K$. We generalize the notion of Hamiltonian orbits:
  Instead of $$\dot{\gamma}(t) = X_H(\gamma(t)) = J \nabla H(\gamma(t)),$$ we require that $$\dot{\gamma}(t) \in J \partial H(\gamma(t))$$ almost everywhere, where $\partial H$ is the subdifferential of $H$, which is well-defined since $H$ is convex. This means that at smooth points of $\partial K$, $\dot{\gamma}(t)$ equals the usual Hamiltonian vector field, while at non-smooth points, $\dot{\gamma}(t)$ lies in the convex hull of the possible Hamiltonian vector fields coming from the adjacent smooth faces.
- If we write our $3$-faces, which is where $\partial K$ is smooth, as
  $$F = \{ z \in \mathbb{R}^4 : \langle z, n_F \rangle = c_F \},$$
  for some normal vector $n_F$ and constant $c_F > 0$, then the Hamiltonian vector field on $F$ is given by
  $$\nabla H(z) = \frac{2}{c_F} n_F,$$
  $$X_H(z) = J \nabla H(z) = \frac{2}{c_F} J n_F.$$
- Thus on each smooth $3$-face $F$, the Hamiltonian vector field is constant in direction, and the flow lines are straight lines parallel to $J n_F$.
- At the intersection of distinct $3$-faces $F_1, \dots, F_k$ that define a $4-k$-face of the polytope, the subdifferential $\partial H$ is given as
  $$\partial H(z) = \text{conv} \left\{ \frac{2}{c_{F_i}} n_{F_i} : i = 1, \dots, k \right\},$$
  for $z$ in the relative interior of the $4-k$-face.

## Minimum Action Closed Characteristics

- For the Viterbo conjecture, we are interested in closed characteristics on $\partial K$ that minimize the action functional $\mathcal{A}$ among all closed characteristics (restricting to the case of positive action). We redefine the action subtly, since the second term equals $T$ on $\partial K$ and thus is the same for all closed characteristics there up to a change of period via reparametrization. So we define:
  $$\mathcal{A}(\gamma) = \int_\gamma \lambda .$$

- Note that for any smooth surface $\Sigma \subset \mathbb{R}^4$ with $W^{1,2}$ boundary $\partial \Sigma = \gamma$, Stokes' theorem gives
  $$\mathcal{A}(\gamma) = \int_\gamma \lambda = \int_\Sigma \omega.$$
  Thus the action of a closed curve can be interpreted as the symplectic area of any surface bounding it.

- This defines a capacity, called the Ekeland-Hofer-Zehnder capacity $c_{EHZ}(K)$:
  $$c_{EHZ}(K) = \inf \{ |\mathcal{A}(\gamma)| : \gamma \text{ is a generalized closed characteristic on } \partial K \}.$$
  Note that the absolute value is necessary since the reversed parametrization of a closed characteristic has the negative action.

- **Theorem:** The minimum is attained, i.e. there exists at least one generalized closed characteristic $\gamma_{\min}$ on $\partial K$ such that
  $$\mathcal{A}(\gamma_{\min}) = c_{EHZ}(K).$$
  **Proof:** Omitted.

- **Theorem:** Generalized characteristics correspond to critical points correspond to periodic orbits up to parametrization. So we have an orbit $\gamma \in W^{1,2}([0,T], \partial K)$ with $\gamma(0) = \gamma(T)$ and $$\dot{\gamma}(t) \in J \partial H(\gamma(t)) = \text{conv} \left\{ \frac{2}{c_{F_i}} J n_{F_i} : \gamma(t) \in F_i \right\}$$ almost everywhere.
  **Proof:** Omitted. 

- Note that on each $3$-face $F_i$, this gives us a constant direction of motion $J n_{F_i}$. But on lower-dimensional faces, we needn't have a constant direction. Heim-Kisliv 2019 however gives us a theorem that at least one minimum action closed characteristic is piecewise linear, moving with constant direction on each $3$-face it visits.

- **Theorem (Heim-Kisliv 2019):** There exists a minimum action closed characteristic $\gamma_{\min}$ on $\partial K$ that is piecewise linear, where each linear segment has a velocity $$\dot{\gamma}(t) = \frac{2}{c_{F}} J n_{F}$$ for some $3$-face $F$ of $K$ with $\gamma(t) \in F$. Note that if $\gamma(t)$ lies on multiple $3$-faces, i.e. $\leq 2$-face, it can pick any of the adjacent $3$-faces for its direction. Furthermore, each $3$-face direction is used for at most one linear segment.  
  **Proof:** See dedicated section. We use Clarke's dual principle to reformulate the minimization problem $\min \mathcal{A}(\gamma)$ on $\gamma \in W^{1,2}([0,T], \partial K)$ as a minimization problem $\min I_K(z)$ constrained to the space $\{ z \in W^{1,2}([0,T], \mathbb{R}^4): \int_z \lambda = 1 \}$. On this space, we can rewrite the path using linear segments (potentially changing the time $T$), and rearrange segments, until we achieve the theorem's statement. The rewrite uses that $J \partial H$ consists of convex combinations of the velocities $\frac{2}{c_F} J n_F$ on the adjacent $3$-faces $F$, and that the action is linear in the path. The rearrangement also uses the linearity. Both steps choose carefully in what order to do the rewrite, and in what order to rearrange, and use that due to symmetry there's at least one choice that will increase the constraint $\int_{z'} \lambda$. We renormalize at the end by $z'' = (\int_{z'} \lambda)^{-1/2} z'$, so that $\int_{z''} \lambda = 1$ again, and note that in the dual minimization problem we have now achieved an equal-or-lower value. This implies that at least one minimum action closed characteristic of the desired form exists, while for higher critical values of the action there may be none of the desired form.

- **Corollary:** The theorem immediately implies that every $3$-face of $K$ is visited (entered and exited) at most once by said minimum action closed characteristic.
  **Proof:** Trivial.

- Heim-Kisliv 2019 now continues in the dual space, and finds an algorithm that does an outer combinatorical search over the order of $3$-face velocities to follow, and an inner linear program to find the time spent with each velocity, so that the resulting path closes, fulfills the dual problem's constraint $\int_z \lambda = 1$, and minimizes the dual problem's functional $I_K(z)$. The global minimum of this algorithm then gives a critical point of the dual minimization problem, which corresponds to a minimum action closed characteristic, thus solving the problem of finding $c_{EHZ}(K)$. The algorithm is described in detail in the dedicated section.

- We use a somewhat different path, to exploit additional sparsity from what combinatorical orders of $3$-faces are possible for Hamiltonian orbits. In practice, this reduces the combinatorical search space drastically and replaces the linear program by a $4$-dimensional fixed-point problem. The algorithm is inspired by Chadez-Hutchings 2021. We use dynamic branch-and-bound search, with a dynamic cutoff for the best action found so far, and a static cutoff for a rotation number constraint that comes from the Zehnder index of the minimum action closed characteristic. The details are in the dedicated section.

## Conley-Zehnder Index of the Minimum Action Closed Characteristic

- First let's introduce the Conley-Zehnder index in the smooth, then the polytope case. We repeat Chadez-Hutchings 2021 here.

- **Fact**: $U(n) = Sp(2n) \cap O(2n)$.
- **Fact**: We can decompose $Sp(2n)$ as $$Sp(2n) = S_+ Sp(2n) \times U(n),$$ where $S_+ Sp(2n)$ are the positive real symmetric symplectic matrices $$S_+ Sp(2n) = \{A \in \mathbb{R}^{2n \times 2n}: J^T A + A J = 0 \land A=A^T \land A \geq 0\}.$$ The universal cover $\widetilde{Sp}(2n)$ decomposes accordingly to $$\widetilde{Sp}(2n) = S_+ Sp(2n) \times \widetilde{U}(n) = S_+ Sp(2n) \times SU(n) \times \mathbb{R}.$$ The determinant $\det: U(n) \to S^1$ lifts to a map $\widetilde{\det}: \widetilde{U}(n) \to \mathbb{R}$. The projection to the $\mathbb{R}$-factor gives us a map $$\rho: \widetilde{Sp}(2n) \to \mathbb{R}$$.
- A geometric interpretation in the case of $n=1$:
  - The universal covering space tracks not just the end deformation, but also the time-dependent path resulting in an end deformation. I.e. we can write elements of $\widetilde{Sp}(2)$ as homotopy classes of paths in $Sp(2)$ starting at the identity.
  - Every $Sp(2)$ matrix can be decomposed into a positive symmetric part $S_+ Sp(2)$ and a rotation part $U(1)$. The positive symmetric part deforms the unit circle into an ellipse, while the rotation part rotates the ellipse. The determinant tracks the rotation angle, up to multiples of $2\pi$. By going to the universal cover, we can track total rotations, i.e. $\mathbb{R}$ instead of $S^1$.
  - Thus $\rho$ tracks for a time-dependent path of $Sp(2)$ deformations how much rotation is done in total.
- In the case of $n=2$, $\rho$ similarly tracks a total rotation, this time from $\det: U(2) \to S^1$. In the case of matrices in $U(1) \times U(1) \subset U(2)$, i.e. diagonal unitary matrices, $\rho$ tracks the sum of the two rotation angles.
- **Definition (Smooth Case):** Pick a smooth Hamiltonian function $H: \mathbb{R}^{4} \to \mathbb{R}$ and a smoothly embedded energy level $\partial K = H^{-1}(1)$, $K = H^{-1}((-\infty, 1]) \subset \mathbb{R}^4$. Let $\gamma \in C^\infty([0,T], \partial K)$ be a periodic orbit of the Hamiltonian vector field $X_H$ with energy $1$, i.e. $\dot{\gamma}(t) = X_H(\gamma(t))$ and $\gamma(0) = \gamma(T)$. The Conley-Zehnder index $CZ(\gamma)$ is defined as follows:
  - Pick a symplectic trivialization of the tangent bundle $\gamma^* T \mathbb{R}^4$ along $\gamma$. This gives us a time-dependent path of symplectic matrices $\Psi(t) \in Sp(4)$ defined by the linearized Hamiltonian flow along $\gamma$, i.e. $$\frac{d}{dt} \Psi(t) = J D^2 H(\gamma(t)) \Psi(t),$$ with $\Psi(0) = I$.
  - Lift $\Psi(t)$ to a path in the universal cover $\widetilde{Sp}(4)$ starting at the identity.
  - This gives us $\rho(\Psi(t)) \in \mathbb{R}$ tracking the total rotation along the path.
  - The Conley-Zehnder index is then defined as $$CZ(\gamma) = \left\lfloor \rho(\Psi(T)) \right\rfloor + \left\lceil \rho(\Psi(T)) \right\rceil \in \mathbb{Z}.$$
- **Properties:**
  - A quick sanity check: The Lie-algebra of $Sp(2n)$ is $J Sym(2n)$, where $Sym(2n)$ are the symmetric $2n \times 2n$ matrices. The flow equation indeed uses such matrices, since $D^2 H(\gamma(t))$ is symmetric.
  - Let $\Phi(t)$ be the change of trivialization, i.e. the path $\Psi(t)$ becomes $\Psi'(t) = \Phi(t) \Psi(t)$ under the change. Since it only changes trivializations, its lift on a loop must be trivial, i.e. $\tilde{\Phi}(T) = I$ in $\widetilde{Sp}(4)$. With additivity of $\rho$ under multiplication, we have
    $$\rho(\Psi'(T)) = \rho(\Phi(T)) + \rho(\Psi(T)) = \rho(\Psi(T)).$$
  - Thus the rotation of a loop, but not an unclosed path, is independent of the trivialization chosen. The Conley-Zehnder index is thus well-defined.
- **Interpretation:** We can pick a trivialization $\{\gamma^* X_H, \alpha \gamma^* n, \gamma^* e_1, \gamma^* e_2\}$ along $\gamma$, where $n$ is the outward normal of $\partial K$ at $\gamma(t)$ and $\alpha(t) \in \mathbb{R}$ some scaling factor. Since $X_H = J \nabla H || n$, we have that $\{X_H, \alpha n\}$ is a symplectic subspace, and thus $\{e_1, e_2\}$ is any symplectic basis of the symplectic complement. The linearized flow now takes the form $$\frac{d}{dt}\Psi(t) \Psi(t)^{-1} = J \begin{pmatrix} 0 & 0 \\ 0 & A(t) \end{pmatrix},$$ where $A(t)$ is a $2 \times 2$ symmetric matrix describing the second derivative of $H$ in the symplectic complement directions. Integrating this flow gives us $\Psi(t) = \begin{pmatrix} I & 0 \\ 0 & \Psi_2(t) \end{pmatrix}$, where $\Psi_2(t)$ is the component on the complement space spanned by $\{e_1, e_2\}$. We have $\rho(\widetilde{\Psi}(T)) = \rho(\widetilde{\Psi_2}(T))$, so the $n=2$ rotation in $Sp(4)$ reduces to the $n=1$ rotation in $Sp(2)$, with the intuitive interpretation of tracking the rotation of the symplectic complement as it's transported along $\gamma$ by the linearized flow.
- **Interpretation (continued):** We can interpret the $Sp(2)$ matrices on the symplectic complement as tracking how the flow lines close to $\gamma$ wind around $\gamma$. For a small tubular neighborhood of $\gamma$, we can write points as $(s, x_1, y_1)$, where $s$ is the coordinate along $\gamma$ and $(x_1, y_1)$ are symplectic coordinates on the symplectic complement with trivialization $\{e_1, e_2\}$. The linearized flow on the complement then describes how nearby flow lines move in the $(x_1, y_1)$-plane as we move along $\gamma$ in $s$. The rotation $\rho$ then tracks how much these nearby flow lines rotate around $\gamma$ in the symplectic complement as we go once around $\gamma$. Note that $\rho$ can be non-integer, since the flow lines needn't close up after one loop around $\gamma$.
- **Definition (Polytope Case):** As we let smoothenings $K_\epsilon$ of the polytope $K$ converge to $K$, it will turn out that the minimum action closed characteristic $\gamma_{\epsilon,\min}$ have a subsequence converging to a generalized minimum action closed characteristic $\gamma_{\min}$ on $\partial K$. Whatever convergence notion we use, it also applies to the induced $Sp(4)$ paths, and their universal covers, and thus the rotation $\rho$ and the Conley-Zehnder index $CZ$. The tricky part is ofc that we need to watch the $\leq 2$ skeleton, since that's where non-smoothness happens. 
  - In the 3-face case, just for completeness sake, we have that $D^2 H$ is $0$, so we have $\Psi(t_1) = \Psi(t_0)$ for times $t_0, t_1$ in the interior of a $3$-face.
  - Instead of a continuous change in $\Psi(t)$, we have jumps when crossing between $3$-faces. Concretely: whenever our velocity jumps $\dot{\gamma}(t^-) = \frac{2}{c_{F_-}} J n_{F_-}$ to $\dot{\gamma}(t^+) = \frac{2}{c_{F_+}} J n_{F_+}$ at time $t$, we have a jump in the linearized flow $\Psi(t_-) $ to $\Psi(t_+)$. If we take the perspective of tracking nearby flow-lines, this jump corresponds to projecting the symplectic component in $F_-$ orthogonal to the velocity direction $J n_{F_-}$ to the $2$-face $F_- \cap F_+$ between $F_-$ and $F_+$, and then projecting it onto the symplectic component in $F_+$ orthogonal to $J n_{F_+}$. Each projection is symplectic wrt the respective restrictions of $\omega$, thus their composition is symplectic as well, giving us the jump matrix $\Psi(t_+) \Psi(t_-)^{-1} \in Sp(2)$ on the symplectic complement.
  - We can compute the Conley-Zehnder index of a generalized closed characteristic $\gamma$ by adding up the rotation increments from each jump between $3$-faces.
  - Above calculation fails only if the projections are not well-defined, which happens only if the velocity is tangent to the $2$-face. In that case, we have that $\{ n_{F_-}$, $n_{F_+} \}$ are lagrangian, and thus the $2$-face is lagrangian as well, with $\omega|_{F_- \cap F_+} = 0$. Intuitively, infinitesimal perturbations perpendicular to the velocity can now lead to flow lines that don't cross the $2$-face at all, i.e. have different combinatorics, and can gain finite distance from the original flow line. The tubular neighborhood picture breaks down. 
  - 
- **Note:** Chadez-Hutchings 2021 shows that any closed characteristic with a linear sigment on a $1$-face is obtained as the limit of smoothings where the Conley-Zehnder index goes to infinity. Consequently, a minimum action closed characteristic cannot have a segment on a $1$-face.
- 


(TODO: I just thought a bunch and realized that CH2021 explicitly assume the case where no faces are lagrangian; in the smooth convex case there never is a problem since the normal $n$ is smooth, and thus $n, Jn$ are a symplectic subspace with a symplectic complement. And the tubular neighborhood stays tubular since the second derivatives are smooth and thus the second difference is locally bounded. I suppose it's worth thinking about whether the CZ index is undefined in the limit if we have lagrangians; we know that there's polytopes with (exclusively) lagrangian 2-faces and they are interesting to look at; they also cannot be turned into non-lagrangian 2-faces via symplectic transformations, we can only wiggle infinitesimally and exploit that while the orbits can be degenerate/highly sensitive to perturbations, the capacity shouldn't be; not sure if the CZ index of orbits is highly sensitive or if a limit exists.)
(The way forward I think is this:
- note that HK2019 applies also to lagrangian 2-faces, while CH2021 assumes the case without lagrangian 2-faces; make clear in lemmas whether they assume non-lagrangian or not.
- explore how the different quantities behave for different infinitesimal perturbations of lagrangian 2-faces; easiest here is to slightly tilt the adjacent 3-faces, i.e. change their normals but not their offsets; this gives us $3$ DOFs for each normal, some of which may not change lagrangianity; we likely get 2 different combinatorics, depending on what direction the Reeb flow now goes through the non-lagrangian 2-face. if we get huge rotation, in a way that doesn't cancel out always, we know that the limit isn't well-behaved. I already expect that the orbits with fixed combinatorics i.e. the fixed-points are sensitive, i.e. huge changes, the capacity isn't sensitive (bc capacity is continuous), the combinatorics of the orbit may be sensitive as well i.e. it changes which combinatorics has the lowest action fixed-point.
)

I'm also pretty unsure about the rotation/CZ definition I gave. Easy to get wrong. Probably worth looking how it's usually introduced, and what other common definitions are equivalent (or equivalent for the generalization to polytopes at least) and worth mentioning.
