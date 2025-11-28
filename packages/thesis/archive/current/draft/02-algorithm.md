# Capacity Algorithm (Draft)

This file is the literal math-level specification of our novel algorithm to compute $c_{\mathrm{EHZ}}(K)$ for convex polytopes in $\mathbb{R}^4$. It is written for a mathematician; no data types or implementation details. Foundational non-smooth symplectic notions (gauge, subdifferential flow, polygonal form, simple-loop theorem, rotation bound) are collected in `docs/draft/01-symplectic-geometry-on-polytopes.md`. All gaps are flagged as TODO; uncertain claims are marked in HTML comments.

## Scope and stance
- Inputs: convex, star-shaped, non-degenerate polytopes $K \subset \mathbb{R}^4$ given by half-spaces $\langle n_f,x\rangle \le b_f$ with outward unit normals $n_f$ and support numbers $b_f>0$; $0 \in \operatorname{int} K$.
- Assumption (strict): every $2$-face is non-Lagrangian; inputs with a Lagrangian $2$-face are rejected upfront. <!-- if we later add Phase B support, adjust this gate -->
- Outputs: (1) the value $c_{\mathrm{EHZ}}(K)$; (2) one minimising closed characteristic as an ordered list of points on $2$-faces that form a piecewise-linear closed path. The search still works with cycles + fixed points; we post-process the winning cycle and fixed point into the explicit point list.
- Floating-point and tolerance policy is intentionally absent here; see TODO.

## Preliminaries and notation
- Symplectic form $\omega_0(u,v)=\langle Ju,v\rangle$ on $\mathbb{R}^4$ with $J=\begin{pmatrix}0&-I\\ I&0\end{pmatrix}$; Liouville form $\lambda_0 = \tfrac12\sum_{i=1}^2(p_i\,dq_i - q_i\,dp_i)$.
- Facet (3-face) $F$: plane $H_F=\{x:\langle n_F,x\rangle=b_F\}$ with outward unit normal $n_F$ and support $b_F>0$; Hamiltonian facet velocity $p_F := (2/b_F) J n_F$ (HK2019). Flow segments are parametrized with $\dot x = p_F$.
- Ridge (2-face) $i=F\cap G$: non-Lagrangian ($\omega_0|_{T_i} \neq 0$). $T_i$ is the tangent plane of $i$; $\pi_i: i \to A_i \subset \mathbb{R}^2$ is an orthonormal, $\omega_0$-positive chart; $\Xi_i$ its inverse affine map.
- Co-facet notation: if $j\subset F\cap G$, write $G(j,F)$ for the unique facet $G\neq F$ with $j=F\cap G$.
- Support function $h_K(u)=\sup_{x\in K}\langle u,x\rangle$; offsets satisfy $b_F = h_K(n_F)$.

## Structural theorems we rely on
- **Simple loop (Haim–Kislev 2019, Thm. 1.5).** There is a closed characteristic with minimal action whose velocity is a finite sequence of positive multiples of facet velocities $p_F$, and each facet is visited at most once. The search is restricted to such facet-simple loops.
- **Rotation bound (CH2021 Prop.~\texttt{ehwz}(b) + Thms.~\texttt{combtosmooth}/\texttt{smoothtocomb}).** There exists an action minimiser with $\rho\le2$; if nondegenerate then $\rho<2$ and $\mu_{\mathrm{CZ}}=3$. The CH correspondence carries this bound to polygonal orbits on symplectic polytopes. We prune as soon as accumulated $\rho\ge 2$ (rotation accumulated by summing the edge increments $\rho_{ij}$ defined below).
- **No 1-face segments (CH2021).** A minimiser with $\mu_{\mathrm{CZ}}=3$ does not contain a segment inside a $1$-face; edges implying such segments are disallowed.
- **Non-Lagrangian ridge orientation.** For a non-Lagrangian ridge $i=F\cap G$, exactly one of $p_F, p_G$ points into $i$ and the other points out; $\langle n_F, J n_G \rangle \neq 0$ certifies this (HK2019, Lemma 3.4).
- **Action of a facet segment.** If $x\in H_F$ flows along $p_F$ for time $\tau>0$, the action increment is $\tau$ because $\langle \gamma(t), n_F\rangle=b_F$ along the segment and $\lambda_0(\dot\gamma)=1$.

## Per-edge first-hit map (geometry only)
- Fix an oriented pair of ridges $i\xrightarrow{F}j$ that both lie in facet $F$.
- Exit time (requires $\langle n_{G(j,F)}, p_F\rangle>0$): for $x\in i$, the first hit of the co-facet $G(j,F)$ occurs at
  $$\tau_{ij}(x)=\frac{b_{G(j,F)}-\langle n_{G(j,F)},x\rangle}{\langle n_{G(j,F)}, p_F\rangle},\qquad \tau_{ij}(x)>0.$$
- Domain $\operatorname{dom}\psi_{ij}$: points of $i$ for which $j$ is the first exit inside $F$, equivalently $\tau_{ij}\le \tau_{ik}$ for every co-facet $k$ with $\langle n_k,p_F\rangle>0$.
- Edge inclusion rule: we include the oriented edge $i\xrightarrow{F}j$ in the search graph only if $\langle n_{G(j,F)}, p_F\rangle>0$ and $\operatorname{dom}\psi_{ij}\neq\varnothing$; otherwise the flow from $i$ along $p_F$ cannot reach $j$ first and the edge is absent.
- Affine first-hit map on ridge charts:
  $$\psi_{ij}: \operatorname{dom}\psi_{ij}\to A_j,\qquad \psi_{ij}(\pi_i(x)) := \pi_j\bigl(x+\tau_{ij}(x)\,p_F\bigr).$$
  Domain and image are convex polygons; the linear part has strictly positive determinant. <!-- need to check if strict positivity ever fails in degenerate-but-nonlagrangian cases -->
- Action increment on $\operatorname{dom}\psi_{ij}$: $A_{ij} = \tau_{ij}$ (affine in $x$).
- Rotation increment $\rho_{ij}$: argument of the orthogonal polar factor of the linear part of $\psi_{ij}$; $\rho_{ij}\ge 0$.

## Return map for a directed cycle
Let $p=(i_1 \xrightarrow{F_1} i_2 \xrightarrow{} \dots \xrightarrow{} i_k=i_1)$ be a directed cycle in the ridge graph.
- Return map: $\Psi_p := \psi_{i_{k-1}i_k}\circ\dots\circ\psi_{i_1i_2}$ acting on the start chart $A_{i_1}$.
- Candidate set propagation: set $C_1 = A_{i_1}$; for each step $t$ set
  $$C_{t+1} = \psi_{i_t i_{t+1}}\bigl(C_t \cap \operatorname{dom}\psi_{i_t i_{t+1}}\bigr).$$
  If some $C_t$ is empty, discard the path.
- Action accumulation: $A_p$ is affine on $C_t$ and updated by pull-back through $\psi_{i_t i_{t+1}}$ and addition of $A_{i_t i_{t+1}}$; all increments are non-negative.
- Rotation accumulation: $\rho_p = \sum \rho_{ij}$ along the path. If $\rho_p \ge 2$, discard the path (Conley–Zehnder index bound from Prop. 1.10(b)).
- Closure test: solve $\Psi_p(z)=z$. If $\det(I-\mathrm{D}\Psi_p)\neq 0$, there is at most one fixed point; accept it only if it lies in $C_1$. If $\det(I-\mathrm{D}\Psi_p)=0$, intersect the affine fixed-point line with $C_1$ and minimise $A_p$ on that intersection (one-dimensional linear program). Reject if the intersection is empty.

## Search strategy (mathematical skeleton)
Depth-first enumeration over ridge cycles, constrained by the simple-loop property and the rotation bound.
1) Choose a start ridge $i$. Initialise $C=A_i$, $A=0$, $\rho=0$, $\Psi=\mathrm{id}$.
2) For each outgoing edge $i\xrightarrow{F}j$ with $\operatorname{dom}\psi_{ij}\neq\varnothing$:
   - Replace $C$ by $C \cap \operatorname{dom}\psi_{ij}$. If empty, skip this edge.
   - Push forward $C \leftarrow \psi_{ij}(C)$.
   - Update $A \leftarrow A\circ\psi_{ij}^{-1} + A_{ij}$ and $\rho \leftarrow \rho + \rho_{ij}$. If $\rho \ge 2$, backtrack.
   - If an incumbent action upper bound $A_{\text{best}}$ is available, intersect $C$ with $\{A \le A_{\text{best}}\}$ and drop the branch if the intersection is empty.
   - If the next node equals the start ridge, run the closure test and, if successful, update $A_{\text{best}}$ and record the cycle.
3) After all outgoing edges are processed, mark the start ridge as done and move to the next start ridge.

## Correctness sketch (non-Lagrangian case)
- Soundness: Every accepted fixed point gives a closed characteristic that follows the recorded cycle because (i) each stored edge is a first-hit map inside a facet, (ii) the composed map matches the flow across the chosen facets, and (iii) solving $\Psi(z)=z$ closes the orbit in the start chart; post-processing the cycle plus fixed point into the explicit piecewise-linear point list does not change the orbit.
- Completeness under assumptions: The simple-loop theorem restricts minimisers to facet-simple cycles; the non-Lagrangian assumption guarantees that every admissible transition appears as some edge; pruning by rotation $<2$ and by non-negative action increments cannot remove the true minimiser whose rotation lies in $(1,2)$.
- Therefore, within Phase A assumptions, the minimum action returned by the search equals $c_{\mathrm{EHZ}}(K)$. <!-- Double-check: do we need an additional argument that the start-ridge enumeration cannot miss the minimizing cycle? -->

## TODOs and deferred cases
- TODO: Formalize the rotation bound and its dependence on Conley–Zehnder index hypotheses; integrate an explicit citation.
- TODO: Lagrangian $2$-faces (currently unsupported: inputs with a Lagrangian $2$-face are rejected). Extend the graph to permit tangential flow with cone maps or perturbations; document the chosen handling and prove that the minimal action value is preserved. HK–Ostrover 2024 show the standard counterexample uses a Lagrangian product (regular pentagon $\times$ 90°-rotated pentagon) whose minimiser runs along Lagrangian $2$-faces; any future Phase B must reproduce that case.
- TODO: Floating-point realization (tolerances, normalization, robustness); link to the numerics policy once written.
- TODO: Alternative upper/lower bounds (LP/SDP from the Haim–Kislev formula) and how they couple to the search for pruning.

## References (reading list)
- Haim–Kislev (2019): simple-loop property and combinatorial formula.
- Chaidez–Hutchings (2021): index/rotation bounds and non-1-face segments; smoothing-to-combinatorial correspondence.
- Haim–Kislev & Ostrover (2024): counterexample via Lagrangian pentagon product; constrains Phase B design. <!-- verify exact citation details -->
