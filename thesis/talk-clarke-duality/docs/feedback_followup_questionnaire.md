# Follow-up Feedback Questionnaire (Clarke Duality Talk)

This file is a follow-up to `docs/feedback_questionnaire.md`, based on your filled answers.
It’s meant to resolve a few remaining ambiguities so the slide deck can be made consistent
and “notation-safe”.

Last updated: 2026-01-11.

---

## Glossary (terms used here)

- **Primal problem**: “minimize action over (generalized) closed characteristics on \(\partial K\)”.
- **Dual problem**: “minimize \(I_K(z)\) over \(z\in E\)” (Clarke dual action principle).
- **Parameterization choice**: whether we talk about *unparameterized* closed characteristics, or *parameterized* Reeb/Hamiltonian orbits with a period \(T\).
- **Existence vs homotopy**:
  - “existence”: there exists at least one minimizer with a property;
  - “homotopy”: a given minimizer (or any minimizer) can be continuously deformed to one with the property (often a stronger claim).

Reply style: fill `Answer:` lines with `a/b/c` or a short sentence.

---

## F1) Take-home slide packaging (Q1 refinement)

You wrote a pipeline take-home (“Clarke ⇒ surprising minimizer property ⇒ computable”).
To reflect that cleanly: what should the *final* slide actually be?

- a) A single theorem statement: “there exists a minimum-action orbit that visits each facet at most once”
- b) A pipeline slide: “Clarke duality → rearrangement → facet-once minimizer → finite/combinatorial optimization”
- c) A computational statement/formula slide (e.g. HK combinatorial formula / “finite QP over facet order + times”)
- d) other: ______
- Answer: b) mainly, no need to restate the theorem, the last slide should be higher-level and more of a reminder of what the audience may now want to ask questions about. don't forget to include a bibliography slide before the final slide or I will forget it haha.

---

## F2) Viterbo context (Q2 refinement)

You currently say you’re unsure, but you also want the HK2024 counterexample picture as motivation.
Pick the *default* amount of Viterbo context you want to plan for:

- a) 1 slide, 2–3 min: “capacity = minimal action; Viterbo conjecture relates capacity to volume”
- b) 2–3 slides, 5–7 min: add “strong Viterbo” + “why polytopes” + counterexample picture
- c) 4–6 slides, 10–12 min: fuller context (but forces cuts elsewhere)
- Answer: c) because it enables people to care about the thesis; tbh i think so far time estimates were high, and we don't run into time issues in the actual talk! no need to cut content *because of time*, only if something is not relevant enough that i would talk about it even if i had 20min left over.

Optional nuance: what is the point of mentioning HK2024 in this talk?
- a) hook: “this matters / conjecture is subtle”
- b) emphasize multiplicity/degeneracy of minimizers
- c) show a concrete polytope to keep things grounded
- Answer: hook a), it is a rather ugly polytope, and the degeneracy is a nice side-note and illustrative but not sth i would want people to remember (asking questions about it may be fine!)

---

## F3) Which orbit concept is the “main object” in the talk?

You want to introduce closed characteristics, Reeb orbits, and Hamiltonian orbits early,
then focus mostly on Reeb (parameterized) and briefly use Hamiltonian for Clarke.

To keep definitions stable: which object should be treated as *primary*?

- a) closed characteristics (unparameterized geometric loops; reparametrization-free)
- b) Reeb orbits (parameterized, period \(T\), \(\alpha(R)=1\) normalization)
- c) Hamiltonian orbits for \(H=g_K^2\) (parameterized; differential inclusion on polytopes)
- Answer: I think I like to talk about Reeb vectors, Reeb orbits the most, by far, and only switch temporarily to the other definitions bc a) is used in the literature and c) is needed for Clarke duality.

Follow-up: should we explicitly state the “closed characteristic = Reeb orbit up to reparametrization” relation?
- a) yes, one slide
- b) yes, but only spoken
- c) no, keep only one notion on slides at a time
- Answer: yes, I really want 1 slide that just compares the 3 different concepts, so people can memorize that they are "basically the same".

---

## F4) Strength of the “simple minimizer” claim

Your answer uses “minimizers are homotopic to…” language, but the safe headline claim is usually an **existence** claim.

Which do you want to claim on slides?

- a) existence only (safe): “there exists a minimum-action orbit with facet-once / connected-velocity-block property”
- b) existence + soft language: “one can simplify a minimizer” (without claiming “any”)
- c) strong homotopy statement (only if you have a precise reference + exact statement)
- Answer:

If you pick (c), point to where the exact statement lives (thesis section / HK2017 theorem number):
- Answer: oh, the homotopy point is like useful to keep in mind! it says a lot about what the minimizer set looks like, namely that we have the simple ones and the rest is connected to them. but I don't want to waste too much time there, it's good enough to mention that all the manipulations we make to the minimizer z (approximation, splitting, growth+shrink) can be done as homotopies. I can give a precise statement if you fail to come up with one after a few attempts! though I think you know enough to state it properly. I guess you can also wrod it as "existence" and then a fact/remark that "moreover, homotopy".

---

## F5) Notation + constant-factor conventions (the “no mistakes” section)

You wrote that this is the hardest part and must be contradiction-free.
Please confirm which convention set we should treat as the single source of truth.

- a) “copy thesis conventions verbatim” (preferred for safety)
  - Source: `packages/latex_viterbo/chapters/math/08-clarke-dual-action.tex`
- b) “copy HK2017 conventions” (adapt thesis text accordingly)
- c) “talk-specific conventions”, but then we must write them down explicitly as a checklist
- Answer: I am not sure if the thesis conventions are correct right now :/ HK2017 has weird conventions that I dislike, mainly the T=1 normalization with extra factors "c" everywhere. So I would go with c) and then in the future after the talk I can maybe fix the thesis where it was wrong.

Concrete checks (fill in / confirm):
1) Liouville 1-form:
   - a) \(\lambda=\tfrac12\langle Jx,dx\rangle\)
   - b) other: ______
   - Answer: yep
2) Dual functional:
   - a) \(I_K(z)=\tfrac14\int_0^1 h_K^2(-J\dot z)\,dt\)
   - b) other: ______
   - Answer: yep I think
3) Constraint set \(E\):
   - a) \(\int_0^1 \dot z\,dt=0\) and \(\int_0^1\langle -J\dot z,z\rangle dt=1\) and \(\int_0^1 z\,dt=0\)
   - b) like (a) but without the \(\int z=0\) constraint
   - c) other: ______
   - Answer: yep, unsure, yep ; centering is useful to avoid trouble with uniqueness of z given \dot z, and to avoid some trouble wrt doing variational arguments for the Clarke dual action principle.
4) Do we want to keep time domain fixed as \([0,1]\) for the dual problem?
   - a) yes (and treat \(T\) as derived by scaling)
   - b) no (keep an explicit period \(T\) in the dual problem too)
   - Answer: I dislike the domain = [0,1], so definitely (b) with a free period T in both primal and dual problems. If I understand correctly (please check and sketch the argument/proof/calculation yourself in a scratch file!) then we need to demand A(z)=T i.e. \int \langle -J \dot z, z \rangle dt = 2 T. This way, we have a correspondence between primal and dual problems where both have the same T. So we get z=gamma-center(gamma). Then the legendre-fenchel inequality gives us
     int_0^T g_K^2(z) dt + int_0^T 1/4 h_K^2(-J \dot z) dt >= int_0^T \langle -J \dot z, z \rangle dt
     so
     T * 1 + I_K(z) >= 2 A(z)
     since we demand A(z)=T we get
     I_K(z) >= T
     with equality iff 
       -J \dot z(t) in \partial g_K^2(z(t)) a.e.
       iff
       z(t) \in \partial 1/4 h_K^2(-J \dot z(t)) a.e.
     so we get equality iff z is a Reeb/Hamiltonian orbit for H=g_K^2.
     The minimizer set is thus the same as before, with minimum I_K(z_min) = T_min = A_min(K) > 0.
     Shortening the time in the proof then goes from a z: [0,T] -> R^2n with A(z)>=T to a z': [0,T'] -> R^2n with T' = T * sqrt(T'/A(z)) and A(z')=A(z) * (T'/A(z)) = T' and I_K(z') = I_K(z) * sqrt(T'/A(z)) <= I_K(z). Solving for T' gives T'=T^2/A(z) < T.

---

## F6) Proof strategy choices (what must be shown vs cited)

You inserted “M5.5 proof of Clarke dual action principle (10–15 min)” and then a long “final theorem” proof sketch.
Given the 60min target speaking time (plus break), we likely need to pick where to spend proof time.

1) Clarke dual action principle proof:
   - a) cite only (statement + intuition + 1 key inequality slide)
   - b) partial proof (key steps; skip technical subgradient/inclusion parts)
   - c) full proof (10–15 min)
   - Answer: full proof, tbh it's pretty simple
     - Legendre-Fenchel; clearly define and discuss the inequality statement, briefly show the calculations
     - clearly define and state the equivalence of the primal and dual problems
     - prove the equivalence:
       - z weak extremal point <=> Euler-Lagrange equation with Lagrange multiplier for A(z)=T constraint
         "d/dt d/d\dot z (1/4 h_K^2(-J \dot z)) = \lambda (-J \dot z)"
         "<=> const = grad (1/4 h_K^2)(-J \dot z) - z"
         "<=> z+const = grad (1/4 h_K^2)(-J \dot z)"
         constraint still needs to be tracked: "A(z)=T"
       - gamma is Reeb orbit <=> 
         "-J \dot gamma = grad (g_K^2)(gamma)" and "g_K(\gamma)=1"
       - per Legendre-Fenchel, the two gradient equations are equivalent
       - one can also see that for Reeb orbits on \partial K, we have A(gamma)=T
       - and for z satisfying A(z)=T we have g_K(z+const)=1
       - thus we indeed have a 1:1 correspondence, with
         z = gamma - center(gamma)
         A(z)=A(gamma)=T
         I_K(z)=T
         g_K(gamma)=1
         on all critical points

2) “Limits work out” (smoothing-limit theorem) emphasis:
   - a) state as a theorem + reference, no proof
   - b) short proof sketch (1–2 min)
   - Answer: eh, we can even be vague about this, it is really not a focus of the talk. I think a picture is the most important thing here, to argue that "sure, one could talk about what happens if we take smoothings K_epsilon -> K, but Jörn promises that all works out just fine, and while we also didn't do all calculations using subgradients instead of gradients, that text-replacement kind of argument works out too so we could just define everything, without worrying whether the limits of e.g. closed characteristics on K_epsilon converge to generalized closed characteristics on K. But it's good to know that our definitions aren't trash but indeed work with the limits."

3) Rearrangement / facet-once theorem proof:
   - a) detailed proof sketch (this is the main proof of the talk)
   - b) medium sketch (only the key inequality + why rearrangement works)
   - c) high-level only + reference (if time runs out)
   - Answer: detailed proof, this is the main interesting result of the talk!

---

## F7) Computation slide (Q8 vs your module M7)

Your Q8 says “none” (no algorithm/pseudocode), but you also wrote an explicit “finite-dimensional search space” slide.

Which do you want?

- a) no computation slide at all (end at “computable in principle”)
- b) 1 conceptual computation slide: variables are (facet order, segment lengths), constraints are “closedness + area”
- c) include formulas/QP framing like you drafted (still no pseudocode, but explicit constraints)
- Answer: eh, it is nice mentioning that we are now down to sth that can be turned into a QP (even if it is not yet right now a QP in the form we write down). The main thing I want to mention is basically the last step of the pipeline proof, namely that we are now in a compact search space of (facet order, segment lengths) under constraints "closedness, area". So I guess it's (b) what you mean? But I think what I drafted is kinda good here? Not sure where between (b) and (c) I want to be, I don't know what exactly you mean. Hopefully I articulated what I mean though.

---

## F8) Figures / assets (operational details)

You want hand-drawn, likely PNG.

1) Storage format:
   - a) PNG (hi-res), as you said
   - b) PDF vector exports when possible (recommended for line drawings)
   - c) mix: PNG for shaded sketches, PDF for line drawings
   - Answer: (a) as I said.

2) Where should these live in the repo?
   - a) `packages/latex_talk_clarke_duality/assets/manual/` (current talk package)
   - b) directly under thesis assets already: `packages/latex_viterbo/assets/manual/`
   - Answer: (a) sounds good.

---

## F9) References slide format (Q11 refinement)

You want full citations.

Pick the format you want on the slide deck:
- a) author + title + year + arXiv id (when available) (compact, unambiguous)
- b) full journal citation (journal/volume/pages) when known + arXiv when applicable
- Answer: arXiv is sufficient for me, all is on arXiV.

If you want (b), please paste journal info for Clarke’s 1979 reference (or tell me to look it up):
- Answer: eh, please use web search, though I think I never read the 1979 reference and only limit myself to HK2019 (HK2017 depending on how you count year numbers on arxiv uploads that got edited), HK2024 (I think it'd be nice actually to cite the journal for this one, iirc it got accepted now in a famous spot?), and CH2021 iirc (Chadez-Hutchings iirc).

