# Next Actions (role-based, self-reviewed, time-boxed)
Temporary planning note; fold into `docs/roadmap.md` or a single GH issue after review, then delete this file to avoid drift.

## Decisions (defaults you can override)
- **Placeholders for capacities/sys & tolerances:** Allowed, but must be replaced within **48h** of introduction. Tests using provisional values must be `xfail/skip` with `reason="TBD/provisional"`.
- **Storage policy:** Default to **git-lfs for artifacts ≤100 MB**; use **/workspaces/worktrees/shared/** for larger or regenerable outputs. Record the final choice in `docs/pm-knowledge-transfer.md`.
- **Single source of truth for this plan:** Once approved, move content into `docs/roadmap.md` (or one GH issue) and delete this file.

## Risks and mitigations
- **Drift from placeholders:** Deadline + xfail tags + tracking issue for each provisional value.
- **Plan sprawl:** Commit to folding this note into an existing plan doc/issue; delete afterwards.
- **Cross-language divergence:** Use one JSON fixture + validator for baseline polytopes; avoid language-specific fixtures.
- **Oversized artifacts in git history:** Storage rule above; large runs go to shared dir.

## Role-based tasks with acceptance criteria and target dates

### Owner (project)
- Approve/record storage rule and placeholder policy in `docs/pm-knowledge-transfer.md`.  
  *Acceptance:* Note added; date: ___.
- Open/assign four issues with owners/dates: tolerances policy; baseline truth set (simplex, cube, crosspolytope, HK2024); sampler defaults (incl. near-lagrangian rejection); Lean axioms list.  
  *Acceptance:* Issues exist with owners and due dates: ___.
- Greenlight porting of legacy spec pieces (oriented-edge, LP/SDP bounds, generator catalogue).  
  *Acceptance:* Decision noted in roadmap/issue: ___.

### This agent (current worktree)
- **Spec tighten (Phase A non-lagrangian):** Update `packages/thesis/src/01-algorithm.mdx` with explicit CZ/rotation definition, tolerances placeholders, and Lagrangian deferral + re-entry trigger.  
  *Acceptance:* File renders; TODOs marked “provisional/TBD”; no broken anchors. Date: ___.
- **AXIOMS skeleton:** Create `packages/lean_viterbo/AXIOMS.md` listing assumed lemmas with citation slots and a “prove later?” flag.  
  *Acceptance:* File <1 page, aligned with spec references. Date: ___.
- **Baseline fixture + validator (shared):** JSON fixture listing simplex, cube, crosspolytope, HK2024 with fields {id, rep (H/V), data, capacity, sys, status=provisional/TBD, citation}; include a small validator usable from Rust/Python/Lean. Seed provisional numbers where available, else TBD.  
  *Acceptance:* Validator passes on fixture; Rust/Python smoke can load it. Date: ___.

### Other agents (separate worktrees; can start once placeholders allowed)
- Rust scaffold: H/V reps, ridge graph, first-hit maps, DFS with rotation pruning; tests load the fixture (TBD-friendly).  
  *Acceptance:* Unit tests run on cube/simplex; no panics.
- Bounds tool: Exact ≤5-facet + LP lower bound; tests on fixture; CLI/lib entrypoint.  
  *Acceptance:* Returns numbers (provisional OK) and exits 0 on fixture.
- PyO3/maturin glue: Minimal integration test calling Rust core.  
  *Acceptance:* Py test passes.
- Sampler configs: JSON schema + test/prod defaults (with near-lagrangian rejection knob); schema tests.  
  *Acceptance:* Validation green; defaults load.
- Lean stubs: Mirror Rust API; reference `AXIOMS.md`; `lake build` green.  
  *Acceptance:* `lake build` succeeds; modules align.

## Dependencies / ordering
1) Owner confirms placeholder + storage policies and opens the four issues.
2) Spec/axioms/fixture work (this agent).
3) Parallel engineering scaffolds consume the fixture; replace provisional values per the 48h rule.

## Alternatives considered
- Single-format fixture vs per-language: chose single JSON+validator to avoid divergence.
- Blocking on exact values vs placeholders: chose placeholders with deadline/xfail to maintain velocity without silent drift.
- Separate plan file vs merging: kept temporary file for review; will merge into roadmap/issue to avoid sprawl.
