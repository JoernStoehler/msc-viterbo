# Research Question
<!-- Style: literal, explicit, rigorous; keep terminology consistent; mark assistant additions with <proposed>. -->

The Viterbo Conjecture was long believed to be true by many, until Haim-Kislev 2024 gave a counterexample in $4$ dimensions. That's the lowest dimension where Viterbo's conjecture is not trivially true, and further counterexamples in higher dimensions can be constructed from the $4$-dimensional one.

We are interested in which convex bodies the Viterbo Conjecture fails and holds, concretely in the computationally feasible case of convex polytopes in $4$ dimensions.
The research question of the thesis is thus to probe Viterbo's Conjecture using computational methods, formulate and falsify hypotheses, and try to formulate conjectures we believe to be true and relevant for future research or for motivating a deeper understanding of symplectic geometry.

## Scope
- Convex polytopes in $\mathbb{R}^4$, with standard symplectic form $\omega_0$ and standard Liouville form $\lambda_0$.
- For a few nicer properties downstream, we move the origin into the interior of the polytope.
- We want to handle both generic cases, and symmetric or otherwise special cases that may have degenerate behavior.
- In particular, we want to handle polytopes with as many facets, and as degenerate behavior, as the standard counterexample from Haim-Kislev 2024.

## Out-of-Scope
- Smooth convex bodies (we only handle polytopes directly; smooth bodies can be approximated by polytopes).
- Other dimensions than $4$ (we only handle $4$ dimensions directly; higher dimensions may behave differently, but are also harder to compute with).
- Non-convex bodies, e.g. merely symplectic convex bodies.
- Other questions about symplectic geometry not related to Viterbo's conjecture and the action of closed characteristics on convex polytopes.

## Sub-Questions

**"How does symplectic geometry work on polytopes?"**

There is existing literature for how to treat the polytope case as a limit of smoothings, but we want to directly reason about the polytope limit and need to gather notations and facts from the literature, and extend them to more tricky edge-cases where the limits behave badly.

**"How do we compute the EHZ capacity of a convex polytope?"**

Existing algorithms exist (Chaidez-Hutchings 2021, Haim-Kislev 2019, Haim-Kislev 2024 with reference to Minkowski Billiards dynamics), but are not optimized enough to handle polytopes with many facets in a high-throughput setting as is needed for data science experiments.

**"What data science methods yield insights into Viterbo's conjecture?"**

We treat Viterbo's conjecture and symplectic geometry as a black box that takes a convex polytope and returns rich data beyond the boolean of whether Viterbo's conjecture holds. Concretely our rich data involves different polytope representations, the EHZ capacity, the volume, one minimum action orbit, and possibly more. On top of the black box we then employ all the data science methods we can think of, to simply try-and-see what yields insights. This includes clustering, dimensionality reduction, anomaly detection, feature importance methods, and more.

**"What rich data is useful for data science methods and what rich data can we compute efficiently?"**

The black box data science methods require us to compute rich data for many polytopes. We will simply try-and-see what data is useful and worth the hassle of developing a computationally efficient algorithm.

**"What insights did we obtain about symplectic geometry and Viterbo's conjecture in particular?"**

We translate our computational findings back into statements about mathematics, in particular as computationally obtained witnesses of existence statements, e.g. of further counterexamples of particular types, and as soft evidence that supports/suggests our hypotheses and conjectures. 

**"Can we prove some of our conjectures?"** 

Besides computational arguments that counterexamples to our conjectures must be rare, we'd like actual arguments that they are non-existent and our conjectures are true. We try to look for insights that inspire proofs, and we look for computationally exhaustive numerical bounding arguments that give us the sharp, or relaxed versions, of our conjectures.

## Viterbo's Conjecture

**Conjecture (false): Viterbo's Conjecture**: For a convex body $K \subset \mathbb{R}^{2n}$, the minimum action $A_{\min}(K)$ and the volume $\mathrm{vol}(K)$ satisfy
$$\mathrm{sys}(K) := \frac{\mathcal{A}_{\min}(K)^n}{n! \mathrm{vol}(K)} \leq 1.$$
Where
$$\mathcal{A}_{\min}(K) = c_{\mathrm{EHZ}}(K) = \inf \{ |\mathcal{A}(\gamma)| : \gamma \text{ closed characteristic on } \partial K \}$$
$$\mathcal{A}(\gamma) = \int_{\gamma} \lambda_0$$
is the action of a closed characteristic $\gamma$ on the boundary of $K$, with $\lambda_0$ the standard Liouville form on $\mathbb{R}^{2n}$.
Instead of thinking through what closed characteristics are in the polytope case, we can also define equivalently
$$\mathcal{A}: W^{1,2}(S^1, \mathbb{R}^{2n}) \to \mathbb{R}, \quad \mathcal{A}(\gamma) = \int_0^{2\pi} \lambda_0(\dot{\gamma}(t)) dt$$
$$\mathcal{A}_{\min}(K) = \inf \{ |\mathcal{A}(\gamma)| : \gamma \text{ critical, non-stationary point of } \mathcal{A} \}.$$
This uses that the critical points are precisely the closed characteristics, plus the stationary curves with action $0$ which we exclude.

**Theorem: Standard Counterexample (Haim-Kislev 2024)**: There exists a $4$-dimensional convex polytope $K \subset \mathbb{R}^4$ with $\mathrm{sys}(K) > 1$.
The polytope is given by: $$ K = P_5 \times_L R_{90^\circ} P_5 $$
where $\times_L$ is the Lagrangian product, $P_5$ is the regular pentagon centered at the origin with circumradius $1$, and $R_{90^\circ}$ is the CCW rotation by $90$ degrees in $\mathbb{R}^2$.
The counterexample has $\mathrm{sys}(K) = \dfrac{\bigl(2 \cos(\tfrac{\pi}{10})(1+\cos(\tfrac{\pi}{5}))\bigr)^2}{2\bigl(\tfrac{5}{2}\sin(\tfrac{2\pi}{5})\bigr)^2} = 1.04721\ldots > 1$.
