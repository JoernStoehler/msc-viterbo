# Lean4 Formalization Playbook

This note is for fast onboarding when turning handwritten symplectic-geometry proofs into Lean4 code.

## Minimal daily workflow
1. **Pick the mathematical slice.** Translate your handwritten notes into short lemmas and structures before opening Lean. Work in `packages/lean_viterbo/ProbingViterbo/...`. If a lemma mixes several concepts (polytope combinatorics, symplectic forms, dynamics), split it so that each Lean file proves one theme.
2. **State the objects first.** Create data structures (see `Geometry/Polytope.lean` and `Symplectic/ClosedCharacteristic.lean`) that capture every parameter the paper argument touches. It is completely fine to leave fields as `Prop` placeholders—having a name for the requirement is more valuable than immediately proving it.
3. **Write type-level scaffolding.** Use Lean to enforce shapes: `structure`, `def`, and `abbrev` declarations line up indices, coercions, and free parameters so the later proof scripts only worry about tactics.
4. **Prove helper lemmas interactively.** Run `lake env lean` or use the VS Code Lean extension. Start the proof with `by` and outline the exact tactic steps in comments so that future agents can continue when you stop.
5. **Refine placeholders.** Once the combinatorial skeleton is in place, replace `admit`/`sorry` blocks with actual proofs. Go from the leaves inward: discharge topological facts about polytopes, then the dynamical lemmas, and finish with the duality argument.

## Lean tips (coming from handwritten experience)
- **Manifold regularity:** avoid introducing differentiability predicates too early. In many steps you only need `IsPreconnected`, convexity, or periodicity facts, which we already model as fields on the `ClosedCharacteristic` structure. Upgrade to `ContMDiff` only when a later lemma demands it.
- **4D linear algebra:** treat `R4` as `EuclideanSpace (Fin 4)`. The helper `PhasePoint` in `LinearAlgebra/R4.lean` converts between phase-space coordinates and the raw vector representation so you can keep proofs readable without constant `Fin` gymnastics.
- **Faces and skeletons:** `Geometry/Polytope.lean` introduces a lightweight `Face` structure whose only job is to keep track of subset relationships and dimensions. When you add concrete polytopes later, extend this structure with combinatorial data (facet normals, adjacency, etc.) rather than rewriting the downstream lemmas.
- **Clarke duality ingredients:** keep the dual problem data (`ClarkeDualData`) close to the action functional. This makes both the primal minimization statement and the dual certificates available in the same Lean namespace, mirroring how the handwritten proof switches viewpoints.
- **Testing proofs:** every time you finish a block, run `lake build` from `packages/lean_viterbo` and wait for `OK` before moving on. If you introduce a new module, make sure it is imported (directly or indirectly) by `ProbingViterbo/Main.lean` so that CI notices it.

## Translating a handwritten proof sketch
1. **Name every object.** Example: “closed characteristic that hits each facet at most once” becomes `ClosedCharacteristic.visitsFaceAtMostOnce`. Even if the actual definition is a placeholder, the name makes the goal state precise.
2. **List hypotheses explicitly.** Instead of writing “let `K` be star-shaped”, add `K : StarConvexPolytope V` as a parameter, together with the ambient vector-space instances. That forces Lean to track every assumption automatically.
3. **Encode the combinatorics.** When a proof uses “faces of dimension ≤ 2”, translate it into `F.affineDim ≤ 2` so that the dimension arithmetic becomes available to `linarith` and `omega` later.
4. **Record the duality inequalities.** The handwritten proof of Clarke’s principle typically produces two inequalities forming a squeeze on the action. Capture them as separate lemmas (`action_le_dual`, `dual_le_action`) first; the “face visited once” theorem then becomes a pure combinatorial deduction in Lean.
5. **Iterate:** once the placeholders compile, gradually replace each `admit` by referencing the precise lemma in mathlib (convexity, measure theory, etc.). Document every nontrivial external theorem with a short doc-string so the next agent knows where it came from.

Whenever you are unsure which file should host a statement, default to the most specific namespace (e.g. a lemma about `Face` should go into `Geometry/Polytope.lean`). This keeps the modules short and makes `import` graphs easier to reason about when scaling up the project.
