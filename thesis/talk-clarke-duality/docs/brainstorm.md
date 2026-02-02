# Brainstorm (Clarke Duality Talk)

This file is intentionally \*unapproved\*. It is a scratchpad for ideas, ordering,
and “module interfaces” (what depends on what).

If something is approved, copy it into `docs/decisions.md` or mark it explicitly
in the slides.

If you prefer giving feedback by editing a file, use:
- `docs/feedback_questionnaire.md`

Last updated: 2026-01-11.

## Constraints (already decided)
- Time slot: 90min including break + interleaved questions.
- Target speaking time: ~60min (slide budget ≈ 40 frames).
- Audience: Augsburg symplectic group (PhD/postdoc/profs), knows basic symplectic/contact,
  but a short notation refresh helps.
- Focus: show the “switch problems via Clarke duality, prove a property on minimizers,
  transfer back” pattern (rather than presenting the full thesis).

## Talk modules with sparse interfaces

Idea: each module has a small interface:
- **Inputs**: minimal definitions/facts needed from earlier modules.
- **Outputs**: what later modules may use (and nothing more).

The goal is that we can:
- drop a module if we run out of time,
- reorder modules if discussion goes one way,
- keep proofs self-contained (no “global” notation soup).

### M0 — One-slide story + agenda (2–3 min)
- Inputs: none.
- Outputs:
  - We care about \(\cEHZ(K)\) as “minimal action of a closed characteristic”.
  - Polytopes make the geometry non-smooth and the search space nasty.
  - Clarke duality rewrites the problem into a constrained minimization of a convex functional on loops,
    and *that* exposes a simplification/rearrangement step.

### M1 — Minimal symplectic/contact refresher (5 min)
- Inputs: audience knows what \(\omega\) is; we just fix notation.
- Outputs (minimal):
  - \((\R^{2n},\omega_0,J,\lambda_0)\).
  - Action \(A(\gamma)=\int_\gamma \lambda_0\) (and the \(\frac12\int\langle -J\dot\gamma,\gamma\rangle\) form).
  - “Closed characteristic = Reeb orbit on \(\partial K\)” (in the smooth case).

### M2 — Convex body + polytope dictionary (5–7 min)
- Inputs: module M1 notation; basic convexity.
- Outputs (minimal):
  - Support function \(\support_K\), gauge \(\gauge_K\), polar \(K^\polar\).
  - Polytope = intersection of halfspaces with facet normals \(n_i\) and offsets \(h_i\).
  - Facet velocities \(p_i \sim J n_i\) (Reeb direction on facet interiors).

### M3 — What breaks for polytopes (and why we want a different formulation) (3–5 min)
- Inputs: M1–M2.
- Outputs:
  - Generalized closed characteristic = differential inclusion on \(\partial K\) (Reeb cone on lower faces).
  - Naive minimization of \(A(\gamma)\) is hard because: infinite-dimensional, reparametrization freedom,
    and hard \(\partial K\) constraint.

### M4 — Convex-analytic “engine room” (Fenchel inequality) (5–8 min)
- Inputs: M2 definitions \(\support_K,\gauge_K\).
- Outputs (minimal):
  - Fenchel inequality (up to constants):
    \[
      \gauge_K^2(x) + \tfrac14\,\support_K^2(y)\ \ge\ \langle x,y\rangle,
    \]
    with equality characterized by subdifferentials / gradients (smooth case).
  - Intuition: \(\support_K\) and \(\gauge_K\) are dual via Legendre/Fenchel.

### M5 — Clarke dual action principle (statement + what it buys us) (8–10 min)
- Inputs: M1 action, M2 support function, M4 inequality vibe.
- Outputs (core interface):
  - Constraint set \(E\subset W^{1,2}\) (mean zero + “area” constraint).
  - Dual functional \(I_K(z)=\tfrac14\int_0^1 \support_K^2(-J\dot z)\,dt\).
  - Punchline: \(\cEHZ(K)=\min_{z\in E} I_K(z)\) and minimizers correspond to minimum-action characteristics
    (up to translation + scaling).
  - Practical punchline: \(I_K\) depends on \(\dot z\), not on the full position constraint \(\gamma\subset\partial K\).

### (Break candidate) — After M5
Reason: the first part ends with “we changed the problem”. The second part starts with “now exploit the new formulation”.

### M6 — Polytope-specific simplification: only finitely many velocities matter (5–8 min)
- Inputs: M2 facet normals/velocities, M5 “\(I_K\) depends on \(\dot z\)”.
- Outputs:
  - On a polytope, \(\support_K\) is piecewise-linear, so \(\support_K^2(-J\dot z)\) is controlled by which facet normals
    are active.
  - Heuristic: minimizers can be taken with \(\dot z\) piecewise constant, taking values in a finite set (facet velocities
    and their convex combinations on lower faces).

### M7 — Rearrangement argument: simplify a minimizer (10–15 min)
- Inputs: M5 dual formulation; M6 polytope discretization intuition.
- Outputs (the “structural theorem” interface):
  - You can reorder / group the velocity segments of a minimizer without increasing \(I_K\)
    (convexity + Jensen/Cauchy-Schwarz style estimates).
  - After rescaling back into the constraint set \(E\), you get a new minimizer with a simpler velocity pattern.

### M8 — Facet-once minimizer theorem (HK) (8–12 min)
- Inputs: M7.
- Outputs:
  - Existence of a minimum-action closed characteristic that visits each facet at most once
    (equivalently: each facet’s velocity block is connected in time).
  - Consequence: the search space becomes combinatorial/finite-ish (facet orderings, plus some continuous parameters).

### M9 — Computational/algorithmic takeaway (optional, 5–10 min)
- Inputs: M8.
- Outputs:
  - What you would optimize over in practice (facet sequence + times/weights).
  - Where numerical methods enter (QP/LP, combinatorial enumeration, heuristics).
  - What this buys for probing Viterbo (context only; keep this module drop-in/drop-out).

### M10 — Wrap-up + open questions (3–5 min)
- Inputs: M5 + M8 (at minimum).
- Outputs:
  - One-sentence summary: “Clarke duality makes the functional depend on velocity; that enables rearrangement; hence facet-once
    minimizers; hence computation/structure.”
  - What remains unclear / next steps.

## Shared vocabulary (keep it small)

Try to keep everything else local to modules. Shared interface should stay small:
- \((\R^{2n},\omega_0,J,\lambda_0)\), action \(A(\gamma)=\int_\gamma\lambda_0\).
- Convex body \(K\), polytope facets \(F_i\), normals \(n_i\), offsets \(h_i=\support_K(n_i)\).
- Support \(\support_K\), gauge \(\gauge_K\), polar \(K^\polar\).
- Dual functional \(I_K(z)=\tfrac14\int \support_K^2(-J\dot z)\), constraint set \(E\subset W^{1,2}\).

Everything else (“generalized characteristics”, subdifferentials, smoothing limits, etc.) is optional / can be pushed into
side remarks if the audience asks.

## Questions I cannot answer myself (fast-to-reply format)

Reply format suggestion: `Q3: b)` or `Q3: b) but ...`.

1. **Q1 — What is the single “main theorem / take-home” slide you want to end the talk on?**
   - a) “\(\cEHZ(K)=\min_{z\in E} I_K(z)\)” (Clarke duality itself is the climax)
   - b) “facet-once minimizer exists” (HK theorem is the climax)
   - c) “finite/combinatorial reduction” (algorithmic viewpoint is the climax)
   - d) other: ______
   - My guess: b) (supported by a) as the key tool.

2. **Q2 — How much Viterbo context do you want?**
   - a) 1–2 slides max (just enough motivation)
   - b) 5–6 slides (state conjecture, why false, why polytopes anyway)
   - c) essentially none (start directly with capacity/minimizers)
   - My guess: a).

3. **Q3 — Speak in general dimension \(2n\), or fix \(n=2\) early?**
   - a) stay in \(2n\) throughout
   - b) do \(2n\) notation but frequently say “think \(n=2\)”
   - c) fix \(n=2\) and only generalize in remarks
   - My guess: b).

4. **Q4 — Convex analysis depth (support/gauge/Fenchel)?**
   - a) treat as black box: state definitions + key inequality, no proof
   - b) prove Fenchel inequality quickly, emphasize geometric meaning
   - c) go fairly deep (subgradients, polar body geometry, etc.)
   - My guess: b).

5. **Q5 — “Generalized characteristics on polytopes” level of rigor?**
   - a) define the differential inclusion and move on
   - b) also state smoothing-limit theorem (“limits of smooth characteristics”)
   - c) avoid the Sobolev/differential inclusion formalism; talk only heuristically
   - My guess: a) (with b) as a backup slide).

6. **Q6 — Where do you want the break (roughly)?**
   - a) after the motivation/setup, before Clarke duality
   - b) right after stating Clarke duality
   - c) after the rearrangement argument (before consequences)
   - My guess: b).

7. **Q7 — Do you want to show the HK2024 counterexample polytope?**
   - a) mention only (no details)
   - b) include 1 slide with the idea + a picture
   - c) skip; it distracts from Clarke duality
   - My guess: a).

8. **Q8 — Do you want any algorithm/pseudocode slide?**
   - a) no, keep it purely conceptual
   - b) 1 slide with “what variables you’d optimize” (facet order + times)
   - c) multiple slides, show computational pipeline
   - My guess: b).

9. **Q9 — Notation preference for the convex dictionary (so slides stay consistent)?**
   - a) \(h_K\) for support, \(g_K\) for gauge (as in thesis chapter)
   - b) \(\support_K\) and \(\gauge_K\) (semantic names)
   - c) other: ______
   - My guess: b) (matches current `main.tex` draft).

10. **Q10 — Citation style on slides?**
    - a) one “sources” slide + tiny citations under borrowed figures only
    - b) explicit citations on theorem slides (Clarke, HK)
    - c) other: ______
    - My guess: a) (matches `docs/decisions.md`).

11. **Q11 — Which Haim--Kislev references should we cite on the key theorem slides?**
    - a) keep it generic: “Haim--Kislev (year)” in spoken form, full bib at end
    - b) precise: pick the exact paper(s) + year(s) for (i) Clarke-duality-in-this-context and (ii) facet-once minimizer
    - c) other: ______
    - My guess: b) (so the slides are unambiguous, even if spoken references vary).

## Old content dump (from `plan.md`)

Kept here so nothing gets lost; feel free to delete once the slide deck stabilizes.

### Modalities
- Slides, with chalk for questions.
- Total 90min time slot, with break in the middle, questions interleaved with post-talk discussion.
- Target audience: research group at Uni Augsburg, all in Symplectic Geometry, PhD students + postdocs + profs.
- Assumed background: know the basics of symplectic geometry & contact topology, but refreshing notation cannot hurt.
- Goals:
  - motivate the problem I + HK2019 ran into.
  - give the high level idea of the “Clarke duality” trick used in my thesis + in HK2019.
  - explain it in-depth so that everyone understands how/why this machinery works (“gears-level model”, “full proof”).
  - use lots of “fake” pictures (3d instead of 4d) to harness visual reasoning of the audience.

### Structure (raw notes)

1. **Introduction & Motivation**
   1. Thesis topic for context: Probing Viterbo's conjecture
      - 4d setting, convex domain in \(\R^4\).
      - define minimum action of closed characteristics on the boundary of smooth convex domains in \(\R^4\).
      - action of curves: \(A(\gamma) = \int_\gamma \lambda_0\).
      - smooth case: \(\alpha = \lambda_0|_{T\partial K}\), Reeb vector field \(R\).
      - minimum action / capacity definition:
        \[
          c_{EHZ}(K) := \inf\{A(\gamma)\mid \gamma \text{ closed characteristic on }\partial K\}.
        \]
      - Viterbo's conjecture (roughly):
        \[
          1 \ge \frac{c_{EHZ}(K)^2}{2!\,\mathrm{vol}(K)}.
        \]
      - Strong Viterbo's conjecture (all capacities agree on convex domains).
      - conjecture is false: counterexample polytope in (HK2024).
      - thesis context: computational approaches for polytopes in 4d.

   2. Extend to polytopes, which are more computationally accessible
      - why polytopes: computationally accessible; limits of smooth domains; dense in convex bodies.
      - define polytope (convex hull / bounded intersection of half-spaces), origin in interior, faces/facets.
      - normals & Reeb vector field exist only on facet interiors; on lower faces we use cones:
        - normal cone \(n_{\mathrm{cone}} = \R_+ \conv\{n_1,\dots,n_m\}\),
        - Reeb cone \(R_{\mathrm{cone}} = J n_{\mathrm{cone}}\).
      - generalized closed characteristic: \(\gamma\in W^{1,2}(S^1,\partial K)\) with
        \(\dot\gamma(t)\in R_{\mathrm{cone}}(\gamma(t))\) a.e.
      - smoothing-limit theorem (optional): generalized characteristics are limits of smooth ones \(K_\varepsilon\).
      - \(c_{EHZ}\) is continuous under Hausdorff convergence; volume too.

   3. Turn into an optimization problem that can be computationally tackled
      - naive constrained minimization: minimize \(A(\gamma)\) over \(\gamma\subset\partial K\) with differential inclusion
        \(\dot\gamma \in R_{\mathrm{cone}}(\gamma)\).
      - issues:
        - \(W^{1,2}\) is infinite-dimensional,
        - reparametrization freedom,
        - hard boundary constraints.
      - idea: find an equivalent minimization problem over a “friendlier” space.

   4. Clarke duality (idea)
      - replace \(A(\gamma)\) with \(I_K(z)=\tfrac14 \int_0^1 h_K^2(-J z'(t))\,dt\), \(h_K\)=support function.
      - constraints: \(\int_0^1 \langle -J z'(t), z(t)\rangle dt = 1\) and \(\int_0^1 z(t)\,dt=0\).
      - point: \(I_K(z)\) depends on velocity \(z'\), not position.
      - show side-by-side equivalence of the two minimization problems; correspondence \(\gamma = a z + b\).

   5. Clarke duality (execution idea via Fenchel duality)
      - for strictly convex domains: identify \(x\in\partial K\) with \(n\in\partial K^\circ\) via \(\langle x,n\rangle=1\).
      - define \(h_K\) (support) and \(g_K\) (gauge), note \(g_K\equiv 1\) on \(\partial K\).
      - \(g_K^2\) and \(\tfrac14 h_K^2\) are Fenchel duals; use equality characterization.
      - use \(-J\dot\gamma=\nabla g_K^2(\gamma)\) for Reeb orbits / parameterized characteristics.
      - bridge identities (schematic):
        - \(\gamma(t)=\tfrac14 \nabla h_K^2(-J\dot\gamma(t))\),
        - \(I_K(\gamma)+T = A(\gamma)\) after integrating \(\langle \gamma,-J\dot\gamma\rangle\).
