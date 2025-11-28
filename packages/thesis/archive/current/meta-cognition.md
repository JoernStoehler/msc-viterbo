# Meta-Cognition Reference for Agents

Purpose: a high-coverage reference on metacognitive strategies (thinking about and steering your own thinking) for planning, coding, proving, designing, and coordinating in this project. Use it to choose, combine, and adapt strategies; keep plans in one canonical place; make assumptions and risks explicit; and timebox placeholders.

Goal (for this doc): maximize expected downstream task performance of future agents who read it once and then plan/execute typical repo assignments with the Read tool. Concretely: expose all major, high-value metacognitive strategy families; give enough guidance to select/combine them by context; avoid missing any commonly applicable family. Brevity is secondary to coverage; add concise evidence/usage notes when they aid selection.

Scope: broad, practitioner-oriented catalogue of major metacognitive strategy families. It is not literally exhaustive, but it aims to list the main families and common high-value tactics so an agent can see and choose them explicitly. Examples mention this project, but the strategies are general.

Acceptance (what “done” means for this doc): an agent can read this page and (a) name multiple strategy families, (b) select and apply suitable strategies to a task, (c) know how to monitor and adjust, (d) understand limitations, and (e) know where to extend the catalogue.

Assumptions: agents read this before planning; plans have a single canonical home (roadmap or one issue); placeholders are timeboxed and tagged; agents keep strategy use explicit in plans.

---

## Meta-log (metacognitive strategies applied to this document)
- Goal restatement & assumption audit: yes (coverage prioritized; brevity secondary).
- Coverage check vs. taxonomy: yes (planning, monitoring/control, regulation, evaluation, learning/retention, debiasing, attention, decision frames, forecasting, prioritization, disagreement resolution, experiments, skill building, threat modeling).
- Alternative generation: yes (survey vs practitioner guide; coverage chosen).
- Failure-mode / pre-mortem: yes (missing families, drift, overuse of heavy methods).
- Red-team/adversarial perspective: yes (added red-team, threat modeling, pair review).
- Evidence pass: yes (evidence snapshots + cheatsheet added for key tactics).
- Stopping rules: yes (add if commonly applicable family missing).
- Single-source discipline: yes (one doc; no duplicates).
- Verify step: yes (checked against taxonomy and gaps).
- Remaining optional work: per-tactic deep evidence summaries beyond current snapshots; external/adversarial review for freshness.

## Major Strategy Families (check coverage)
- Planning / Setup: goal restatement, assumption audit, alternative generation, criteria definition, decomposition, checklist/template selection.
- Monitoring / Control: pre-mortem/red-team, confidence calibration, monitoring cues & pivot triggers, timeboxing, eager vs. lazy evaluation, attention allocation, single-source discipline.
- Regulation / Adjustment: owner & dependency mapping, risk/mitigation pairing, forcing functions, perspective switching, research passes, simplification/abstraction, chunking of subproblems.
- Evaluation / Reflection: acceptance criteria, verify step, post-mortem/retrospective, playbook updates, ask-for-help.
- Learning / Retention: self-testing, spacing, interleaving, teaching/rubber-ducking, elaboration, dual coding.
- Debiasing: inversion, outside view/reference class, consider-the-opposite, and checks for confirmation/anchoring/availability/sunk-cost/status-quo; decision hygiene (independent inputs, order effects).
- Attention / Environment: reduce interruptions, batch notifications, focus windows, timers, stable seeds/envs, context-switch minimization.
- Decision Frames: OODA for fast loops; Cynefin for domain classification (clear/complicated/complex/chaotic) to pick appropriate tactics.

## Strategy Catalogue (high coverage)
- **Clarify / Goal restatement:** restate objective, scope, constraints, “done.”
- **Assumption audit:** list unknowns/guesses; convert to decisions with owners/dates.
- **Alternative generation:** produce at least one viable alternative per key choice; pros/cons.
- **Criteria definition:** acceptance criteria, success/failure signals, value vs. cost.
- **Decomposition:** chunk work; order by dependencies/critical path.
- **Checklist / template selection:** pick a prebuilt checklist for the task type (planning, code review, proof, experiment).
- **Pre-mortem / red-team:** imagine failure; list causes; add mitigations/checkpoints.
- **Forcing functions:** require answers to prompts (“simpler path?”, “counterexample?”, “inverse claim?”) before finalizing.
- **Confidence calibration:** compare confidence to evidence; adjust scope if thin.
- **Monitoring cues & pivot triggers:** define signals that mean “switch strategy” (e.g., repeated arguments, unresolved assumptions, time overrun).
- **Timeboxing / pacing:** set budgets for tasks and for TBD placeholders; expire provisional values.
- **Eager vs. lazy evaluation:** run cheap probes early (load docs, smoke tests); defer low-value work until prerequisites settle.
- **Owner & dependency mapping:** who does what, in what order; surface blockers.
- **Risk/mitigation pairing:** every major risk gets a mitigation or checkpoint.
- **Stopping rules / decision thresholds:** define “stop analyzing when…” (e.g., best alternative clearly ahead, time budget hit, marginal gain small).
- **Single-source discipline:** one canonical plan location; merge/delete duplicates to avoid drift.
- **Perspective switching:** PM, domain expert, adversary, reviewer to find blind spots.
- **Research / evidence pass:** pull concrete data (prior code, papers, logs) before committing to a plan.
- **Simplify / abstract:** restate at a higher level; remove non-essentials; find invariants.
- **Chunking & scaffolding:** build small scaffolds or stubs to reduce working-memory load.
- **Externalization:** write assumptions, decisions, and checkpoints; don’t rely on memory.
- **Acceptance & verify step:** define “done” and verify each chosen step was performed.
- **Post-mortem / reflection:** capture what worked/failed; update templates/checklists.
- **Ask for help:** explicitly request inputs/decisions that gate progress.
- **Self-testing / spacing / interleaving:** quiz yourself; space reviews over time; mix task types to strengthen retention.
- **Rubber-ducking / teaching:** explain the plan/idea aloud or to another agent to expose gaps.
- **Debiasing moves:** inversion, base rates, consider-the-opposite, note sunk-cost risk.
- **Attention & environment control:** dedicated focus blocks, timer use, minimize context switches, stable seeds/envs in experiments.
- **Reference class forecasting / outside view:** compare to similar past tasks and their outcomes.
- **Decision frames:** pick a frame suited to context—OODA (Observe–Orient–Decide–Act) for fast loops; Cynefin for classifying domains (clear/complicated/complex/chaotic) and choosing appropriate strategies.
- **Elaboration / dual coding:** connect concepts with examples/analogies; pair words with visuals to improve understanding and recall.
- **Implementation intentions / WOOP / backcasting:** state if–then triggers (“If I hit blocker X, I will do Y”), mentally contrast desired outcome vs. current obstacles, and plan backward from the goal.
- **Checklists & standard work:** reuse or adapt checklists (à la Checklist Manifesto) to reduce omissions and variability.
- **Forecasting hygiene:** independent estimates before group discussion; median/trimmed means; avoid anchoring on first numbers; use reference classes.
- **Probability calibration:** express uncertainty with ranges/probabilities; compare to base rates; track forecasts vs. outcomes to calibrate.
- **Mental simulation / red-team run-through:** simulate the plan step-by-step (or with an adversarial perspective) to surface gaps.
- **Deliberate slowing / System 1 vs. System 2 awareness:** notice when fast intuition is driving; insert a slow check for high-stakes steps.
- **Cognitive load management:** limit active threads; jot intermediate results; stage work to keep working memory free.
- **Decision logging:** note key decisions, rationale, and evidence to aid later review and reduce hindsight bias.
- **Deliberate practice loop:** focused practice on weakest subskill with feedback; small increments (Ericsson).
- **Concrete examples:** pair abstractions with specific examples; works with dual coding.
- **Fermi/rough estimation:** quick order-of-magnitude checks to bound solutions.
- **Prioritization heuristics:** MoSCoW (Must/Should/Could/Won’t), RICE/ICE scores, expected value vs. effort to rank tasks.
- **Explore–exploit balancing:** when uncertain, allocate some effort to explore alternatives; then exploit the best-known option.
- **Scenario planning / branches:** outline a few plausible futures and pre-plan responses; useful when stakes are high and uncertainty broad.
- **Bias checklist (common):** confirmation, anchoring, availability, sunk-cost, status-quo, halo/horn, uniqueness/inside view, overconfidence, recency. Use debiasing moves above to counter.
- **When not to overuse:** skip heavyweight pre-mortems/decision hygiene for trivial/low-stakes tasks; scale strategy effort to stakes and uncertainty.
- **Argument mapping / double crux:** map claims, evidence, and disagreement points; identify the “double crux” that would change minds fastest.
- **Disagreement decomposition:** list cruxes (empirical, definitional, value); plan targeted tests or clarifications.
- **Pre-registration / hypothesis checks:** for experiments, preregister hypotheses, metrics, analysis plan to reduce HARKing and researcher degrees of freedom.
- **Sampling / stopping discipline (experiments):** define sample size/stop rules up front; avoid peeking-driven bias.
- **Guardrail metrics:** define “don’t break” constraints (perf, latency, safety) alongside primary metrics.
- **Pair/peer strategies:** pair planning/review, adversarial (devil’s advocate) passes, and rubber-ducking to surface blind spots.
- **Decision/forecast log:** record forecast ranges, rationale, evidence, chosen strategies; review later for calibration.
- **Red-team / adversarial pass:** assign an adversarial reviewer to find holes on high-stakes items (code, proofs, experiments).
- **Inside vs. outside view sanity:** always pair an inside-view plan with a reference-class check; adjust estimates accordingly.
- **Base-rate tables:** keep quick base rates for common tasks (bug fix time, test flake rate, experiment failure rate) and consult them.
- **Escalation triggers:** define in advance when to escalate (time overrun, confidence below X, unowned blockers).
- **Simplify-to-core (MVP/MVS):** strip to a minimum viable plan/spec to get feedback fast while respecting guardrails.
- **Sensitivity analysis:** vary key assumptions/inputs to see impact on decision; identify fragile assumptions.
- **Risk register:** list risks with likelihood/impact/owner/mitigation; track over time.
- **MCDA / utility weighting:** make criteria explicit; weight and score options (e.g., weighted decision matrices, expected value with constraints).
- **EV / EVSI checks:** compute expected value of options and of additional information (is more data worth it?).
- **Power/MDE planning:** size experiments; compute minimum detectable effect; avoid underpowered tests.
- **Data/seed/version control:** lock data versions, seeds, envs to ensure reproducibility; log configs.
- **Threat modeling:** identify assets, adversaries, attack surfaces; apply to security-sensitive/code review contexts.

## How to Use (practical recipe)
1) Clarify goal/constraints and acceptance.
2) Assumption audit → decisions with owners/dates.
3) Generate alternatives; pick with rationale.
4) Pre-mortem: list ≥3 failure modes; add mitigations/checkpoints.
5) Owners/deps: assign, order, and timebox; set placeholder expiry.
6) Single source: choose the canonical location; remove duplicates.
7) Execute probes: quick evidence (docs, code, smoke tests); adjust.
8) Monitor: watch cues; pivot if triggers fire.
9) Verify: check you actually applied the steps above.
10) Post-mortem: note lessons; update checklist if warranted.

### Strategy selection guide
- High risk/novel task: favor pre-mortem, assumption audit, alternatives, evidence pass, perspective switching, debiasing.
- Ambiguous ownership: prioritize owner/dependency mapping, single-source discipline.
- Heavy uncertainty/TBDs: enforce timeboxes, xfail/skip tagging, checkpoints.
- Need speed with safety: eager probes, timeboxing, minimal viable plan, verify step.
- Learning/retention needed: self-testing, spacing, interleaving, rubber-ducking.
- Attention scarce: environment control, timers, chunking, simplify/abstract.
- Fast-moving / high uncertainty: consider OODA; for mixed domains, use Cynefin to pick suitable tactics.
- Analysis paralysis: set stopping rules/decision thresholds; pick simplest viable plan; timebox analysis.
- High-stakes decisions: add deliberate slowing, probability ranges, base rates, mental simulation, and a recorded decision log.
- Forecasting tasks: use outside view/reference classes, independent estimates, aggregation (median/trim), and calibration tracking.
- Prioritization tasks: use expected value vs. effort, MoSCoW, or RICE/ICE scoring; consider explore–exploit balance if uncertainty is high.
- Skill building: deliberate practice loop, concrete examples, dual coding, spaced retrieval.
- Research/evidence gathering: allocate a fixed timebox; start with highest-signal sources; record what would change your mind; log cites.
- Code/proof/design: small spikes/prototypes; counterexamples; invariants; checklist pass; verify obligations.
- Disagreement resolution: argument map, list cruxes, seek “double crux,” run targeted tests/clarifications, log outcomes.
- Team sync/review: pair planning or adversarial review for high-stakes items; use checklists to structure review.
- Experiments: preregistration, power/MDE sizing, stop rules, guardrails, seed/data versioning, sampling discipline.
- High-uncertainty models/forecasts: sensitivity analysis; EV/EVSI; MCDA/utility weighting if multiple criteria.
- Security/critical changes: threat modeling; red-team; guardrail metrics; escalation triggers.

## Examples of Application
- **Planning a feature/experiment:** clarify scope; assumption audit (data availability, tolerances); alternatives (roadmap vs issue); pre-mortem (drift, TBD rot, missing owner); mitigations (single source, 48h placeholder expiry); owners/deps; acceptance tests; verify.
- **Proof/design task:** clarify claim; assumption audit (definitions, lemmas); alternatives (direct vs contrapositive vs induction); pre-mortem (hidden cases, dependence on unproven lemma); mitigations (small cases, counterexamples); checkpoints; verify against acceptance.
- **Debugging/triage:** clarify failure signal; assumption audit (what changed); alternatives (repro path variants); pre-mortem (red herrings, environment drift); mitigations (isolate env, record seeds); checkpoints; verify fix via tests.
- **Forecasting/estimation:** clarify forecast target; assumption audit (base rates?); independent estimates; outside view/reference class; aggregation; calibration log; timebox; verify against outcomes.
- **Prioritization:** list options; estimate value/impact and effort; apply EV vs effort, MoSCoW, or RICE/ICE; pre-mortem (wrong bet); mitigations (explore small sample before scaling); decide; log rationale.
- **Skill-up plan:** identify weakest subskill; design short deliberate practice loop with feedback; use spaced retrieval and interleaving; log practice; review progress weekly.
- **Research pass:** define question and “decision impact”; 30–90 min timebox; gather 3–5 high-signal sources; note assumptions and what would change your mind; log citations; stop when diminishing returns hit or timebox expires.
- **High-stakes decision:** clarify decision; assumption audit; bias checklist; outside view/base rates; independent estimates; mental simulation; pre-mortem; set stopping rule; decide; log rationale and probabilities; schedule review.
- **Code/PR review:** clarify acceptance; assumption audit (requirements, interfaces); checklist (naming, errors, tests, docs); pre-mortem (regressions, perf); mitigations (tests, feature flags); verify; decision log.
- **Resolving a disagreement:** map claims/evidence; list cruxes; identify double crux; gather targeted evidence; update; log what changed minds.
- **Experiment design:** preregister hypotheses/metrics/analysis; power/MDE and sample size; guardrails; seeds/data versions; stop rules; run; log; analyze per prereg; report with calibration.
- **Risk register:** list risks with likelihood/impact/owner/mitigation; review regularly; escalate per triggers.
- **Sensitivity sweep:** vary key inputs/assumptions to see impact; focus mitigation/measurement on fragile drivers.
- **Threat modeling (security/critical):** identify assets, adversaries, attack surfaces; define mitigations and tests; red-team high-risk paths.

## Task-Specific Quick Checklists
- **Planning / Roadmap item**
  - Clarify objective/scope/acceptance.
  - Assumptions → decisions; owners/dates.
  - Alternatives; choose with rationale.
  - Pre-mortem (3+ risks) → mitigations/checkpoints.
  - Owners/deps; single source; timebox TBDs.
  - Verify, decision log, post-mortem.
- **Experiment / Data run**
  - Question & success metrics; prereg where useful.
  - Assumptions: data quality, seeds, tolerances.
  - Plan: config, seeds, hardware, budget, storage.
  - Pre-mortem: drift, leakage, underpowered run → mitigations.
  - Run small probe; log seeds/config; monitor; verify reproducibility.
  - Archive artifacts + provenance; post-mortem.
- **Proof / Design**
  - Clarify claim/definitions.
  - Assumptions: known lemmas; gaps.
  - Alternatives: direct, contrapositive, induction, invariants.
  - Pre-mortem: hidden cases, dependence on unproven lemmas.
  - Work small cases/counterexamples; track obligations; verify.
- **Debugging**
  - Clarify failure signal; reproduction path.
  - Assumptions: what changed? env vs code.
  - Alternatives: repro variants; isolate components.
  - Pre-mortem: red herrings, flaky env.
  - Mitigations: pin env/seeds, bisection, logging.
  - Verify fix; regression test; decision log.
- **Forecasting / Estimation**
  - Define target/metric/time horizon.
  - Outside view/base rates; reference classes.
  - Independent estimates → aggregate (median/trim).
  - Record ranges/probabilities; calibration log.
  - Stopping rule; compare to outcomes later.
- **Prioritization**
  - List options; estimate value/impact/effort.
  - Score (EV, RICE/ICE, MoSCoW).
  - Pre-mortem: wrong bet; run small explore if needed.
  - Decide; log rationale; set review point.
- **Code / PR Review**
  - Clarify requirements/acceptance; read diff end-to-end.
  - Checklist: correctness, errors, edge cases, perf, security, readability, tests, docs.
  - Assumptions/unknowns → questions.
  - Pre-mortem: likely regressions; mitigations: targeted tests/flags/metrics.
  - Decide/approve with notes; log follow-ups.
- **Disagreement Resolution**
  - Clarify the claim/decision at issue.
  - Argument map: claims, evidence, assumptions.
  - List cruxes (empirical/definitional/value); identify double crux.
  - Gather targeted evidence/tests; update.
  - Log what changed minds; note remaining disagreement.

## Evidence Snapshots (why these work)
- **Pre-mortem / prospective hindsight:** ~30% more risks identified vs. status-quo review (Klein et al.).
- **Retrieval practice & spacing:** robust improvements in retention and transfer; spacing beats massed practice (Learning Scientists synthesis).
- **Checklists:** reduce omissions/variability in high-stakes domains (Gawande).
- **Reference class forecasting:** reduces optimism/uniqueness bias (Kahneman & Lovallo; Flyvbjerg et al.).
- **Independent estimates + aggregation:** improves forecast accuracy vs. group discussion first (Tetlock & Gardner; Noise).
- **Implementation intentions / WOOP:** measurable gains in goal follow-through (Oettingen).
- **Deliberate practice:** focused, feedback-driven practice builds skill faster than naive repetition (Ericsson).
- **Decision hygiene (Noise):** separating judgments, ordering, and aggregation reduces variance in expert judgments.
- **Dual coding / elaboration:** combining verbal + visual/explanatory links improves comprehension/recall (Learning Scientists).
- **Mental contrasting:** clarifies obstacles and increases follow-through (Oettingen).
- **Pre-registration / sampling discipline:** reduces HARKing and biased peeking in experiments (open-science practices).
- **Argument mapping / double crux:** makes disagreements explicit and solvable via evidence; reduces talking past each other.
- **Independent review/pairing:** independent passes catch more issues than groupthink; adversarial review surfaces blind spots (broad code review literature).
- **Deliberate practice:** targeted practice with feedback outperforms naive repetition (Ericsson).
- **Implementation intentions:** if–then planning boosts goal follow-through (Oettingen).
- **Decision hygiene / independent estimates:** separating judgments and aggregating improves forecast accuracy and reduces noise (Noise; Superforecasting).
- **Red-team/adversarial review:** uncovers hidden failure modes in high-stakes contexts (security/code review practice).
- **Reference classes/base rates:** reduce optimism and uniqueness bias; improve calibration (Kahneman & Lovallo; Flyvbjerg).
- **Sensitivity analysis:** highlights fragile assumptions; guides where to invest measurement/mitigation (Saltelli et al.).
- **Power/MDE planning:** avoids underpowered experiments; increases detection of true effects.
- **MCDA/weighted scoring:** makes trade-offs explicit and reduces implicit bias in multi-criteria choices (Keeney & Raiffa).
- **Threat modeling:** structured adversarial thinking finds security/privacy failure modes early.
- **Rubber-ducking / teaching:** explaining to another improves error detection and understanding (learning-by-teaching effect).
- **Spacing + interleaving:** outperform blocked/massed practice on long-term retention and transfer (learning science meta-analyses).
- **Timeboxing / stopping rules:** reduce procrastination and analysis paralysis; increase throughput (productivity studies).

## Quick Evidence Cheatsheet (by tactic)
- Planning: pre-mortem (+30% risks); checklists (fewer omissions); outside view (reduces optimism bias).
- Learning: retrieval + spacing + interleaving + dual coding (higher retention/transfer); deliberate practice (faster skill gain).
- Decision/forecast: independent estimates + aggregation (better accuracy); calibration tracking; reference classes (less optimism/uniqueness bias); decision hygiene (less noise).
- Execution control: timeboxing/stopping rules (limits analysis paralysis); guardrails (protect constraints).
- Experiments: prereg/stop rules (less p-hacking/peeking bias); sampling discipline (valid inference).
- Collaboration/disagreement: argument mapping/double crux (focus on crux), pair/adversarial review (more issues found).
- High-stakes builds: red-team/adversarial pass; guardrails; escalation triggers.
- Modeling/estimation: sensitivity sweeps; base-rate tables; Fermi bounds.
- Multi-criteria choices: MCDA/weighted scoring + EV/EVSI for clarity and bias reduction.
- Security/critical: threat modeling, adversarial review, guardrails, escalation triggers.

## Pre-mortem for This Reference
- **Perceived completeness:** Readers assume exhaustive coverage. Mitigation: explicit non-exhaustive note; pointers to extend.
- **Drift / duplicates:** Multiple planning docs diverge. Mitigation: single-source policy; delete/merge duplicates.
- **Placeholder rot:** Provisional values linger. Mitigation: timebox TBDs; require xfail/skip tags.
- **Vague tasks:** Missing acceptance/owners. Mitigation: require criteria and owner mapping in plans.
- **Overconfidence:** Strategies used without evidence. Mitigation: include calibration and evidence passes.
- **Missing strategy family:** If a commonly applicable family is discovered missing, add it with justification and update the family list.

## Alternatives Considered
- **Long academic survey** vs. **concise practitioner guide**: chose practitioner guide; cite anchors.
- **Per-role variants** vs. **single shared palette**: chose single palette to reduce divergence.
- **Static vs. updateable examples**: core strategy list stable; examples can change with project process.

## Pitfalls to Avoid
- Multiple divergent plans; resolve to one source.
- Unstated assumptions; treat as decisions.
- Open-ended TBDs; timebox and tag provisional tests.
- Vague tasks; add acceptance criteria and dates.
- Overconfidence; check evidence vs. risk/novelty.
- Skipping verification; run the verify step.
- Overusing heavyweight methods for trivial tasks; keep strategy effort proportional to stakes/uncertainty.
- Ignoring bias checklist when stakes are high.

## What this doc does not cover
- Exhaustive academic coverage of metacognition/learning science; consult external sources for depth.
- Domain-specific technical strategies (e.g., algorithmic design patterns); this page is about steering your thinking.
- Tooling/process policies that may change (plan home, storage); see roadmap/PM docs.
- Full checklists for specialized domains (e.g., formal proof checklists, security reviews); bring your own domain checklists and pair them with these meta strategies.

## Maintenance
- Location: this is the single meta-cognition reference; don’t duplicate elsewhere.
- When to update: only if adding/removing a strategy with justification, adding a missing commonly applicable family, or if project process examples (plan home, placeholder tagging) change.
- Who: any agent; keep edits concise and action-oriented.
- Review rule: one structured review (including verify) per edit; revisit after significant use to capture lessons.
- How to extend: if you find a missing commonly applicable strategy family, add it with a short description and (ideally) an anchor reference; keep the document readable within ~10 minutes.

## References (anchor sources)
- Flavell, 1979 — foundational work on metacognition (monitoring/regulation).
- Nelson & Narens, 1990 — monitoring/control framework.
- Boyd, J. — OODA loop (fast adaptive decision cycle).
- Snowden & Boone, 2007 — Cynefin framework for domain classification.
- Kahneman, Lovallo, 1993; Flyvbjerg et al., 2024 — Reference class forecasting and decision hygiene; uniqueness bias.
- Kahneman, Sibony, Sunstein, 2021 (“Noise”) — decision hygiene to reduce judgment variability.
- Klein, G. — Pre-mortem (prospective hindsight for risk surfacing).
- Learning Scientists (Weinstein & Sumeracki et al.) — six evidence-based learning strategies (spaced, retrieval, interleaving, elaboration, dual coding, concrete examples).
- Gawande, 2009 — Checklist Manifesto (checklists to reduce omissions/variability).
- Tetlock & Gardner, 2015 — Superforecasting (probability estimates, aggregation, hygiene).
- Oettingen et al., 2010 — Mental contrasting / WOOP; implementation intentions.
- Kahneman, 2011 — Thinking, Fast and Slow (System 1/2, slowing for high-stakes judgments).
- Larrick, 2004 — Debiasing techniques.
- Ericsson et al., 1993 — Deliberate practice.
- Open Science Collaboration, 2015 — Pre-registration and reproducibility practices.
- van Gelder — Argument mapping/double crux approaches.
- Saltelli et al., 2008 — Global sensitivity analysis.
- Keeney & Raiffa, 1993 — Decisions with Multiple Objectives (MCDA).
- Morgan & Henrion, 1990 — Uncertainty: base rates, sensitivity, and decision analysis.
- OWASP, STRIDE — Threat modeling approaches.
*** End Patch***"}***
*** End Patch !***"},
