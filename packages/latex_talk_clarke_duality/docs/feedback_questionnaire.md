# Feedback Questionnaire (Clarke Duality Talk)

Goal: make it easy to give feedback by editing a file instead of answering in chat.

Follow-ups / clarifications (after first pass):
- `docs/feedback_followup_questionnaire.md`

Guidelines
- Short answers are great (single letter `a/b/c`, plus 1–2 words nuance if needed).
- If you are unsure, leave blank; I’ll interpret blanks as “default guess is OK for now”.
- If you want something explicitly approved, copy it into `docs/decisions.md`.

Last updated: 2026-01-11.

---

## Glossary (planning terms used in this file)

- **Take-home slide**: the one slide you want the audience to remember most at the end.
  It can be a theorem statement, a “bridge” statement (“we changed the problem”), or an algorithmic punchline.
- **Module**: a chunk of slides that can stand mostly on its own and only depends on a few earlier definitions/facts.
- **Keep / Optional / Cut**:
  - `keep`: you want it in the default talk.
  - `optional`: include only if time / discussion allows.
  - `cut`: do not plan for it.
- **Facet-once minimizer**: shorthand for the structural statement “there exists a minimum-action closed characteristic
  that visits the interior of each facet at most once” (equivalently: each facet-velocity appears in one connected time block).
- **Rearrangement argument**: shorthand for “we can reorder/group the velocity profile of a minimizer in the dual problem
  without increasing the dual functional, then rescale back into the constraint”.

## A) Quick choices (copy/paste friendly)

Fill in with e.g. `Answer: b)` or `Answer: b) but ...`.

### Q1 — Main take-home slide (what should the audience remember at the end?)
- a) Clarke duality itself: \(\cEHZ(K)=\min_{z\in E} I_K(z)\)
- b) Facet-once minimizer exists (HK structural theorem)
- c) Finite/combinatorial reduction viewpoint
- d) other: ______
- My default: b)
- Answer: I want the audience to remember: "Clarke Dual Action Principle is useful sometimes, because it reframes the problem in a different form, and allows even rather surprising looking properties about minimizers to be proved, such as that the minimum action closed characteristics are homotopic to piecewise linear paths that use each facet Reeb direction at most once. Which then finally makes everything computable."

### Q2 — Viterbo context amount
- a) 1–2 slides (just motivation)
- b) 5–6 slides (conjecture + false + why polytopes)
- c) none (start at capacities/variational reformulation)
- My default: a)
- Answer: Unsure! Why would I know this already?

### Q3 — Dimension framing
- a) stay in \(2n\) throughout
- b) \(2n\) notation but frequently say “think \(n=2\)”
- c) fix \(n=2\), generalize only in remarks
- My default: b)
- Answer: Dimension is always 4, but it does help to mention that everything generalizes to 2n dimensions.

### Q4 — Convex analysis depth (support/gauge/Fenchel)
- a) black box: defs + key inequality only
- b) quick proof + geometric meaning
- c) deeper: subgradients/polars/etc
- My default: b)
- Answer: a correct definition & geometric meaning via pictures. I think we need subgradients as the technical tool, but more as a "and we can make everything work for Generalized closed characteristics as well".

### Q5 — “Generalized characteristics on polytopes” rigor
- a) define the differential inclusion and move on
- b) also state smoothing-limit theorem (as a fact)
- c) keep it heuristic only
- My default: a) (with b) as backup slide)
- Answer: We definitely need to state that limits work out!

### Q6 — Break placement
- a) before Clarke duality
- b) right after stating Clarke duality
- c) after rearrangement argument
- My default: b)
- Answer: I think it's good to do the break before we state & show the final "simple orbit" theorem in fullness.

### Q7 — HK2024 counterexample polytope
- a) mention only
- b) 1 slide + picture
- c) skip entirely
- My default: a)
- Answer: mention as part of the Viterbo conjecture context, show a picture, but don't dwell on it. Mention that there's multiple minimum action generalized closed characteristics.

### Q8 — Algorithm/pseudocode content
- a) none (conceptual talk only)
- b) 1 slide: “what variables you’d optimize” (facet order + times/weights)
- c) multiple slides: show full computational pipeline
- My default: b)
- Answer: none, we are happy with showing that the problem reduces to a finite combinatorial optimization problem.

### Q9 — Notation style for convex dictionary
- a) \(h_K\) support, \(g_K\) gauge (thesis style)
- b) `\support_K`, `\gauge_K` (semantic names)
- c) other: ______
- My default: b)
- Answer: latex uses h_K because NO MAGIC!

### Q10 — Citation style on slides
- a) 1 sources slide + tiny figure credits only
- b) explicit citations on theorem slides (Clarke, HK)
- c) other: ______
- My default: a)
- Answer: 1 is I think standard.

### Q11 — Pick exact HK references (so theorem slides are unambiguous)
- a) keep spoken reference generic; full bib at end
- b) pick exact paper(s) + year(s) for:
  - (i) Clarke dual action principle in this context:
  - (ii) facet-once minimizer / rearrangement:
- c) other: ______
- My default: b)
- Answer: Full citation because everything else is silly as fuck.

---

## B) Module selection (sparse-interface talk)

This section is self-contained (no need to read anything else). If you want the longer rationale,
see `docs/brainstorm.md`.

Legend: `keep | optional | cut`

- M0 — One-slide story + agenda (2–3 min)
  - Content: what problem, what tool (Clarke), what structural consequence (rearrangement/facet-once).
  - Decision: "what problem" is a bit much to do for the full audience, but definitely we can state the general topic: symplectic geometry, we are looking for closed curves on energy surfaces (picture) i.e. a minimization problem, and we now want to have some theorem that there is at least one minimizer that is piecewise linear & visits each facet only once. The talk is about a proof from the literature, worked out to only rely on master-level pre-knowledge.
  - Notes:
- M1 — Minimal symplectic/contact refresher (5 min)
  - Content: fix \((\R^{2n},\omega,J,\lambda)\), define action, name “closed characteristic / Reeb orbit”.
  - Decision: I think it makes sense to also mention Hamiltonians, Hamiltonian flow, energy surfaces. All in the smooth setting first.
  - Notes:
- M1.5 - Viterbo Conjecture
  - Content: minimum action of closed characteristics = symplectic capacity (no proof), state the Viterbo conjecture, and the strong version, mention that it generalizes to non-smooth convex bodies, e.g. polytopes, and then reveal the counterexample (statement, picture).
- M2 — Recap polytopes
  - Content: support, gauge, polar; polytope facets \((n_i,h_i)\); facet Reeb vectors \(2/h_i J n_i\); standard Hamiltonian \(H(x)=g_K^2(x)\) and Hamiltonian vector field;
  - Decision: small calculations each time to show that signs + constant factors all work out correctly. Pictures! (3D pictures ofc, for illustration and not for correctness)
  - Notes:
- M3 — What breaks for polytopes (3–5 min)
  - Content: lower dimensional skeleton of 0,1,2-faces; subdifferential set instead of gradient in Hamiltonian, convex combination of facet Reeb vectors; differential inclusion formulation of generalized Reeb orbits / generalized Hamiltonian orbits / generalized closed characteristics; normal cone, Reeb cone, convex set of Reeb directions; Pictures!
  - Decision: slide with comparison of the 3 types of orbits (Reeb/Hamiltonian are parameterized with period T, closed characteristics are unparameterized i.e. inclusion has a \R_+ freedom). Emphasize that generalized closed characteristics always exist on polytopes.
  - Notes:
- M3.5 - So what's the issue? 
  - Content: State the "primal" minimization problem (see later slide!) and explain why we don't immediately have a computational approach: we are in a Sobolov space (bad to represent computationally) and have a constraint that is hard to enforce (naive local minimization leads to point orbit which has zero action but is not a closed characteristic). 
  - First theorem: there are minimizers that are (in fact: there are action-preserving homotopies of any generalized closed characteristic to a curve that is) piecewise affine with velocities equal to facet Reeb vectors, with potentially infinitely many breakpoints.
  - Second theorem (today's main surprise): there are such minimizers that assume each facet Reeb vector as velocity at most once (in fact: action-preserving homotopies to such, but only for minimizers not for all generalized closed characteristics).
  - The first theorem can be done by some geometric argument about how we can approximate any path using piecewise affine paths, even while following all constraints (\partial K, action-preserving).
  - The second theorem is more surprising: why would the minimizers be connected in such a way? why not have a minimizer that "loops twice" around the polytope, visiting some facet twice? There needn't a-priori be any way to move the orbit around continuously to become simple. And indeed there needs to be sth about the "global minimum" in there, because for non-minimum generalized closed characteristics we needn't be able to homotopy them to simple ones.
- M3.7 - What's the Solution?
  - Content: We switch from our "primal" minimization problem to a "dual" minimization problem, which then allows us to manipulate the critical points more easily, i.e. yield Theorem 1 & 2 above.
- M4 — Legendre-Fenchel basics (5–8 min)
  - Content: the one convex-analytic inequality and what it “means” geometrically.
  - Decision: general statement; then formulas and pictures for the 1d case of legendre-fenchel duality as a reminder; then specialization to our 1/4 h_K^2 and g_K^2 pair; only the gradient case i.e. strict convexity, we can mention subgradients later / in a copied-and-modified slide version each time.
  - Notes:
- M5 — Clarke dual action principle (8–10 min)
  - Content: repeat the "primal" problem statement; then state the "dual" problem statement; state the correspondence theorem: critical points correspond to each other, in particular minimizers;
  - Decision: It is an utter nightmare to formulate this right! ALL and I mean ALL notation choices must be correct or the final result ends in contradictions. E.g. whether to use periods, whether to use factors like 1/4, when to define free variables and how to say what they depend on, strict convexity, etc. It is crucial that NO MISTAKES are made here. Several AI agents have failed at this and submitted wrong versions that they were adamant were error-free.
  - Notes:
- M5.5 - Proof of Clarke dual action principle (10-15 min)
  - Content: argue through the inequalities here, show that both problems are indeed equivalent, if we pick the right conventions this should work out fine;  
- Break (5-10 min)
- M6 — Final Theorem: piecewise linear minimizers that visit each facet at most once (15–20 min)
  - Content: state theorem; sketch proof; we use the "dual" problem here because we don't have to worry about \partial K constraints.
    - Proof:
      - pick a minimizer \(z\) of the dual problem; we know from Clarke duality that I_K(z) = \cEHZ(K) = T.
      - step 1: any \(z \in W^{1,2} \) can be approximated wrt \(||.||_{W^{1,2}}\) by a piecewise affine orbit \(z'\) with velocities that are convex combinations of facet Reeb vectors. We later have as \(z' \to z\) that \(I_K(z') \to I_K(z)\) and \(A(z') \to A(z)\).
      - step 2: we can split these constant mixed velocity segments into smaller segments with pure facet Reeb vector velocities;
      - for pure paths z'' we have I_K(z'') = T.
      - if we reverse the splitting order for some segment, that flips the sign of the change in action A(z'')-A(z'); let's pick the order such that A(z'') >= A(z'). We could also pick a more detailed split such that A(z'')=A(z') exactly.
      - step 3: for duplicate facet velocities, we can now shrink one and grow the other; I_K is unaffected; A(z''')-A(z'') again flips sign if we switch which one we grow/shrink; so we can choose the order to ensure A(z''') >= A(z''). Note that we cannot do a trick here to pick A(z''') = A(z'') straightforwardly, but >= is enough when dealing with minimizers as we see next.
      - step 4: we now have I_K(z''') = I_K(z), A_K(z''') >= A_K(z'). The constraints of closedness, centeredness are still fulfilled easily. We can now rescale z''' to have A_K(z'''') = A_K(z) exactly by reducing the segment lengths proportionally without changing the velocities. This gives I_K(z'''') = I_K(z''') / sqrt(A_K(z''')/A_K(z)). Since however z was a minimizer, we must have I_K(z'''') >= I_K(z), so we must have A_K(z''') <= A_K(z). Together with A_K(z''') >= A_K(z') and A_K(z') -> A_K(z) as z' -> z, we get A_K(z''') -> A_K(z) as well, and thus I_K(z'''') -> I_K(z) as z' -> z.
      - step 5: the set of piecewise affine paths with velocities equal to facet Reeb vectors and each facet used at most once is a compact set in the following sense:
        Psi: z'''' |-> (order of facets used, lengths of segments)
        This implies that there is a minimizer in this set, with I_K(z^*) = lim I_K(z)
      - step 6: looking back, we can build a homotopy from z to z^* in the set of weak minimizers
- M7 — Computational takeaway (optional, 5–10 min)
  - Content: the search space of the dual problem is now finite-dimensional:
      - (facet order, segment lengths) (sigma, t_i)
      - we can write the conditions explicitly:
        - closedness: sum_i t_sigma(i) 2/h_sigma(i) J n_sigma(i) =!= 0
        - centeredness: /
        - action: A(z) = sum_{1 <= i < j <= m} t_sigma(i) t_sigma(j) omega(2/h_sigma(i) J n_sigma(i), 2/h_sigma(j) J n_sigma(j)) =!= 1
        - optional: we can further restrict to t_i >= 0
        - I_K(z) = 1/4 sum_i t_i h_K^2(-J 2/h_i J n_i) = sum_i t_i
      - this can be reformulated as a quadratic program over (sigma, t_i) (omitted here)
      - various information can be used to further constrain the search space, mainly that we know adjacency relations of facets such that not every pair or longer subsequence of facet velocities is possible
- M10 — Wrap-up (3–5 min)
  - Content: recap main takeaway: Viterbo Conjecture context; Clarke duality switches to a nicer problem; we could then homotope minimizers to simple piecewise affine ones; which finally gives us a computational approach.
  - Decision:
  - Notes:

---

## C) “Must include” / “Must avoid”

### Must include (bullets)
- 

### Must avoid (bullets)
- 

---

## D) Figures / visualizations

1. **Hand-drawn vs TikZ vs imported PDFs**
   - Preference: Hand-Drawn everything! (probably as png pictures in high res, KISS and let's save time)
   - Notes:

2. **Which 1–2 “fake pictures” do you want as anchor visuals?**
   - (e.g. “reordering velocities”, “support function geometry”, “polar polytope”)
   - Choice 1:
   - Choice 2:
   - Eh, I will bring a list of pictures once asked; wayyy more than 2 pictures are needed and wanted;
   - Mainly we will do pictures that show a fake "3d" version of the situation, since 4d pictures are too hard to draw ;). Sometimes even a 1d version is enough, especially if we have e.g. time + space and want to illustrate how to approximate paths / the rearrangement arguments with an explicit time axis instead of just flows in space.

---

## E) Terminology / wording preferences

Fill in only if you have strong preferences; otherwise I’ll keep current draft style.

- “closed characteristic” vs “Reeb orbit” phrasing:
- Use “capacity” early, or delay until after definitions:
- Any notation you strongly dislike:

- We will mostly work with closed characteristics & Reeb orbits & Hamiltonian orbits at the start since i do not know what the audience is most familiar with of the 3 very equivalent concepts. Then we mainly just look at Reeb orbits i.e. parameterized with period T and differential inclusion. For the Clarke duality statement we will ofc have to (briefly) use the Hamiltonian formulation.
