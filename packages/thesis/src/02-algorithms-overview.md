---
title: Algorithms for EHZ Capacity of Convex Polytopes
slug: algorithms-overview
summary: Known and new algorithmic approaches to compute c_EHZ(K) for 4D convex polytopes.
---

# Algorithms for EHZ capacity of convex polytopes
<!-- Style: literal, explicit, rigorous; mark assistant additions with <proposed>. -->

There are a few existing algorithms. They all require as input a compact convex polytope with origin in its interior. They compute as output the EHZ capacity c_EHZ(K), and all except Haim-Kislev 2019 also compute a minimum action closed characteristic.

**Algorithm: Haim-Kislev 2019**: The algorithm solves a combinatorial and quadratic optimization problem over the facets of $K$. It is numerically stable for "most" polytopes, where we can define "most" relative to some simple random distribution over polytopes. It is still numerically stable for "most" polytopes with Lagrangian, or numerically close to Lagrangian, ridges ($2$-faces). The paper does not specify how to obtain a minimum action closed characteristic, only the value of c_EHZ(K).

**Algorithm: Chaidez-Hutchings 2021**: The algorithm solves a combinatorial optimization problem over the facets of $K$. It is numerically stable again for "most" polytopes. It is no longer numerically stable if any ridges are numerically close to being Lagrangian. It is not defined for polytopes that have exactly Lagrangian ridges.

**Algorithm: Minkowski Billiards (used by Haim-Kislev 2024)**: For convex polytopes that are Lagrangian products of $2$-dimensional convex bodies, the EHZ capacity can be viewed as a path-length minimization problem on the first Lagrangian factor, where the metric is given by the polar dual of the second Lagrangian factor. This yields a computationally efficient algorithm for Lagrangian products of $2$-dimensional convex bodies, which includes the standard counterexample above. The algorithm is numerically stable for "most" such Lagrangian products.

Our novel algorithms extend mostly Chaidez-Hutchings 2021 to be more computationally efficient, and to handle polytopes with Lagrangian ridges robustly.

**Algorithm: Stoehler 2025 I**: Requires, as in Chaidez-Hutchings 2021, a convex polytope that has at least one minimum action closed characteristic which does not pass through any ridges that are numerically close to Lagrangian. We make explicit here that instead of rejecting the polytope, we can reject the Lagrangian ridges and then consider separately the case where they are passed through by all minimum action closed characteristics. The algorithm computes c_EHZ(K) and a minimum action closed characteristic by solving a combinatorial optimization problem over the facets of $K$, similar to Chaidez-Hutchings 2021, but with various improvements and implementation optimizations that make it faster and more numerically stable.

**Algorithm: Stoehler 2025 II**: Fallback, works under the assumption that all minimum action closed characteristics pass through at least one ridge that is numerically close to Lagrangian. The algorithm is stable for "most" such polytopes again. Conceptually, the algorithm introduces an infinitesimal ($\mathbb{R}[\varepsilon]$-valued) perturbation of the Lagrangian ridges, and more carefully handles the non-Lagrangian ridges that are close to being Lagrangian. The algorithm then follows "Stoehler I" closely, using the infinitesimal/small-perturbation reasoning to resolve numerical instabilities.

Together, our two novel algorithms can compute c_EHZ(K) and a minimum action closed characteristic for "most" convex polytopes, including "most" polytopes with Lagrangian or approximately Lagrangian ridges. We simply run both, and take the lower action result that is returned.
