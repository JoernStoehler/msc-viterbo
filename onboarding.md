<!-- onboarding.md: Temporary scratch aggregation for commenting; will be replaced by per-package docs and a minimal root AGENTS. -->
<!-- comments are from codex agent #1 -->
<!--J comments are from Jörn Stöhler (project owner) and were written in time after codex was done with its comments -->


<!-- source: AGENTS.md -->
# AGENTS.md

<!-- Meta: Consider adding a 5–10 line "Start here (for every task)" quick-start above, then keep package/folder specifics in their own files. The concatenated mega-file is great for review but heavy for agents; a generated, task-scoped digest would keep instruction count low. Once docs are split per package, keep the root tiny and treat any combined view as a convenience snapshot, not source of truth. -->
<!--J I suggest the root AGENTS.md explains that we are in a monorepo for a master thesis, that AGENTS.md, agent_docs/, packages/*/AGENTS.md, packages/*/agent_docs/ contain further onboarding information for agents, with files containing factual and procedural knowledge and instructions that were bundled according to what tasks need and don't need the information (progressive disclosure); not sure if there's anything else to say here in AGENTS.md that isn't better places in a package's onboarding files, or in agent_docs/ bc task-specific knowledge instead of universal knowledge; i guess mentioning where the sole development environment we use is defined; maybe mentioning the git worktree location; maybe the commuication norms since all agents communicate with Jörn (but they can probably be trimmed a lot and e.g. agents needn't know about agents as much?). -->

## Project Overview
Monorepo for the MSc thesis **"Probing Viterbo's Conjecture"** (code, experiments, proofs, thesis, tooling, environment, agents). Agents work in a single defined devcontainer; GitHub issues/PRs coordinate the work.

Repo layout (top level):
- `packages/rust_viterbo/`: Rust library.
- `packages/python_viterbo/`: Python experiments/pipelines.
- `packages/lean_viterbo/`: Lean4 formalization.
- `packages/latex_viterbo/`: LaTeX thesis stack.
- `.devcontainer/*`, `scripts/*`: environment definition and convenience scripts.
- `AGENTS.md`, `agent_docs/`: onboarding (progressive disclosure).
<!-- Repo map comment: Could auto-generate this list from a shallow `tree -L 2` in CI to prevent drift and surface new folders (e.g. data/, assets/, .github/). Maybe add one-line guidance per package on "when to open" to match the breadcrumb philosophy. -->
<!--J unsure if we even need a repo map; auto generation of this kind of high-impact files is quite fragile and i'd avoid it -->

The onboarding docs require explicit diff-level approval from the project owner due to their importance for future agents.
Other files in the repo can be changed via normal PRs and high-level project owner review.
<!-- Policy clarity: Define what counts as onboarding (e.g., AGENTS.md + agent_docs/*) and whether small typo fixes also need owner approval. Could enforce via CODEOWNERS + status checks to make the rule self-documenting and remove cognitive load. -->
<!--J yep, AGENTS.md + agent_docs/* in root and packages/*/ count; I think above information needs to be moved though anyway to a agent_docs/ file that's about writing onboarding docs -->

## Worktrees
- Main worktree: `/workspaces/msc-viterbo`; additional worktrees under `/workspaces/worktrees/<name>`.
- Create: `git worktree add /workspaces/worktrees/<name> <branch>` then run `scripts/worktree-prepare.sh /workspaces/worktrees/<name>` once (wires Rust target, Lean caches, uv deps).
- Shared caches: see `agent_docs/maintain-environment.md`.
- Remove safely with `git worktree remove /workspaces/worktrees/<name>`.
- GitHub CLI: always use `--body-file` for issues/PRs; include footer `Written-by: codex agent running in worktree <path>`.
- Only the project owner approves PRs targeting `main`.
<!-- Worktree ergonomics: Consider a single script (e.g., `scripts/worktree-new.sh <branch>`) that creates + prepares + prints next steps to cut these bullets to one instruction. Also add guidance on naming (feature/<topic>-<yyMMdd>?), default branch to base from, and cleanup of stale shared caches to prevent disk bloat. A quick health check command (`scripts/worktree-doctor.sh`) could verify symlinks and mounts. -->
<!--J agreed, instead of worktree-prepare.sh have a single worktree-new.sh that replaces git worktree add <path> <branch> + worktree-prepare.sh <path> with better checks etc. a doctor script can be useful, not sure (?) it probably is good documentation anyway so let's have worktree-doctor.sh as well -->

## Universal Conventions
<!-- Instruction budget: This block is dense with must-do behaviors. Might split into "defaults" vs "ask owner when" and convert some into facts/examples to reduce imperative load. Consider a compact checklist + links to rationale files so agents can skim. -->
<!--J yeah it's too dense, and has too many instructions that are not worth writing down in a universal file -->
<!-- Keep patterns popular: prefer ready-made, common flows over custom repo-unique ones (e.g., use standard tool CLIs before adding wrappers; if a wrapper is needed, name it conventionally and keep it thin). This lowers instruction cost and leverages agent muscle memory. -->
<!-- For tests, consider per-package defaults (e.g., python: `uv run ruff check && uv run pytest -q tests/smoke`; rust: `cargo clippy --workspace --all-targets && cargo test -q`; lean: `lake build -q`). Keeps expectations clear without long prose. -->
<!--J yeah, agreed, this isn't sth that goes into universal, but into package's onboarding docs e.g. the develop-code.md or whatever files -->
- **Communication**: Be literally correct, specific, unambiguous. Escalate blockers and repeat unanswered questions; do not assume silence is approval. Disclose progressively to respect project owner time.
- **Quality**: This is a thesis: prioritize mathematical correctness. Code targets senior developers; keep APIs clean, simple, idiomatic. Request reviews from project owner for complex or high-stakes changes.
- **Testing**: Catch errors and regressions early. Use static analysis (linters, type checkers) and runtime tests (unit, integration, e2e) as appropriate per package. Document manual test procedures in comments/docstrings where not automated.
- **Documentation**: Explain the “why” in comments/docstrings; avoid legacy/migration lore entirely.
- **Agents**: Agents are first-class contributors. Agents have zero prior context about the project, but are already familiar with all popular toolchains, frameworks, patterns and domain knowledge. Always err strongly towards the common, boring, simple solution that agents have been trained on, instead of a custom, superficially clever, complex solution. Immediately fix incorrect or ambiguous or missing documentation. It is important that agents can rapidly onboard themselves without having to question and verify the correctness of documentation.
<!-- Possible improvement: Add "what not to do" examples (e.g., avoiding framework reinvention, avoiding large refactors without owner sync) since negative space clarifies intent. Also define testing minimums per package to avoid over-testing paralysis. -->
<!--J good idea. hmm. yeah, i think we shouldn't talk too much about agents in AGENTS.md, but we should have some agent_docs/ about best practices when picking architectures and dependencies where we mention that "add popular large library" is cheap but "custom unique tiny script" is costly bc agents don't have to learn the former but have to learn the latter -->
<!-- Also clarify when to stop and ask (e.g., semantics-changing refactors, new dependencies, math definitions) vs when to proceed autonomously. Reduces decision friction. -->
<!--J yep, that's actually the better policy anyway; instead of teaching agents from scratch the unique complex skill of knowing how to design the repo for agents robustly, just teach them the cheap 80% for 20% of the cost, and importantly teach them when to stop and ask the project owner! -->

## Project Owner
Jörn Stöhler. Expert background in mathematics, machine learning, data science, ai agent design, scientific writing.
<!-- Contact clarity: Add preferred contact channel (repo issues? comments on PR? direct chat?), timezone/availability, and escalation expectations. Helps agents decide when to block vs proceed. -->
<!--J I am always there when agents work, and agents (like you) can just end their turn and write a final message to tell me sth, to which I respond and then they proceed. I think agents know this? from training? thoughts on this? -->

## Subagents
- Run `codex exec "<prompt>" 2>/dev/null` to spawn a fresh agent in the cwd with zero prior context. The subagent can take actions, and will write a text message to stdout once done. Useful for delegating a subtask that is clearly defined and scoped to a known list of files, that is doable for agents without complex context about the ongoing task, and that has too many or too conceptually different steps to be worth doing directly in the main agent. Examples of subagent tasks: semantic search or comparison where many files need to be read but only a small text message needs to be returned; executing a refactoring across many files that is too tricky for mere text-replacement; reviewing the staged changes with fresh eyes.
<!-- Improvement: Provide a 3-line decision rule for when to spawn subagents vs not, plus a template prompt. Consider logging subagent runs (command + stdout) to a temp file for traceability and to help owner review. -->
<!--J agreed. also maybe we just do a scripts/subagent.sh <prompt> that hides the internals and can be introduced as "delegate a task by spawning a new agent under the hood" and "read agent_docs/subagent.md for best practices" -->

## Where to Go Next
- Run `pwd && git status -sb` to confirm your worktree.
- Run `ls agent_docs/` to see available onboarding docs.
- Skip files that are not relevant to your assigned task and read them once they become relevant.
- Ask the project owner if you have any questions about your assigned task, or if you need context beyond what is in the onboarding docs.
<!-- Discovery nudge: also skim `scripts/` (and package-local `scripts/`) for thin wrappers around multi-step flows; treat them as hints rather than instructions, and prefer native commands when wrappers add no value. -->
<!-- agreed. Maybe the first command should be scripts/hello.sh that runs (and prints the commands) a full listing of all relevant folders; that's way quicker to say than ANDing multiple commands together. definitely costs us 1 instruction, btu the avoided trouble from having agents learn dynamic information about the repo is well worth that! -->
<!-- Navigation breadcrumb: Might link the most commonly needed docs per package (e.g., "Python quickstart: agent_docs/develop-python.md"), plus a one-liner "if your task mentions X, open Y" table. Could also add a `scripts/where-to-read.sh` that echoes tailored links based on a keyword (rust/python/latex/lean/devops). -->
<!--J we can have a What To Read Next section in AGENTS.md that explains files better if needed. But tbh "Python: quickstart: agent_docs/develop-python.md" is a waste of our instruction budget, because that's just self-evident from the file names. -->

<!-- source: agent_docs/develop-lean.md -->
# Developing in Lean
<!-- Lean onboarding focus: Provide a minimal "do this first" command block (cd, scripts/worktree-prepare.sh, lake build) to reduce confusion. Also state update policy for Lean/mathlib pins and how to request bumps; otherwise agents may hesitate to pull newer mathlib lemmas. -->
- Package: `packages/lean_viterbo`
- Goal: Formalizing our mathematical results in Lean4 using mathlib4 for verification.
- Toolchain: Lean 4.25.0 (elan default set to `leanprover/lean4:v4.25.0`), mathlib pinned via lakefile. It's a recent stable version.
- Caching: We cache dependencies via the symlink `.lake/packages -> /workspaces/worktrees/shared/lean/packages`. Build output is shared at `/workspaces/worktrees/shared/lean/build-global` via the `.lake/build` symlink.
- Commands: `lake build -q` for normal work; search the mathlib4 docs/source as needed. Run the root prep script `scripts/worktree-prepare.sh <worktree>` to link caches before building.
<!-- Possible addition: point to a canonical search workflow (e.g., `lake exe docs`, use `#find`, or grep mathlib source) since agents often fumble lemma discovery. Also mention how to regenerate cache links if broken. -->
- Quality: We must pass `lake build` without errors. `sorry` in proofs is allowed temporarily, or with explicit documented permission from the project owner. We target the same quality as mathlib4 itself. We document the why behind design decisions in code comments, and reference the thesis writeup's notation where definitions correspond or where they differ.

<!--J TBH we should deprecate Lean. It was nice to set up but isn't actually useful :/ writing Lean4 is just too hard. I suggest to keep it in the git history but otherweise delete it from the current commit i.e. delete the folder packages/lean_viterbo/, onboarding text about it, and environment setup for it (installations, cache folders, etc). Thoughts? -->

## Tips
- The syntax of mathlib changed a lot, and agents have almost-right-but-wrong intuitions. Expect to spend time reading mathlib4 docs and source code while iterating until you get the right types and lemmas.
- To not be overwhelmed by errors, write one file and fix its errors before proceeding to the next.
- Do not revert back and forth when choosing a definition; ask the project owner for help if you are unsure which definition is doable and most useful for later work.
- We want Lean code to read similar to our thesis writeup. Pick similar types and notation where possible, and discuss differences with the project owner, and document the differences and rationale in code comments.
<!-- Could add a short list of "common Lean traps in this repo" (universe levels, coercions with nnreal/reals, measure theory imports, etc.) plus a link to any existing local helpers. That might save repeated search time. -->

<!-- source: agent_docs/develop-python.md -->
# Developing in Python
<!-- Python onboarding: Provide a canonical "fresh worktree quickstart" block (uv sync/install, env activation not needed with uv run, sample test run) to reduce choices. Note uv version: consider pin + update policy. Also maybe point to a central README in `packages/python_viterbo/` for per-experiment breadcrumbs so this section can stay shorter. -->
<!--J that kind of info ideally should've been automated away. agents should only be started in worktrees AFTER the full worktree-new.sh has ran, i.e. after uv sync already ran. And package updates etc can go into a agent_docs/ file about dep management or devops or sth for the package -->
- Package: `packages/python_viterbo`
- Goal: Orchestration layer and logic of quickly written experiments/pipelines.
- Toolchain: Python 3.12.3, uv 0.4.20. Dev extras install `pytest`, `pyright`, `ruff`, `maturin`.
- Caching: `uv` has a global cache. Worktrees have local `.venv` virtual environments.
- Commands: Use `uv run` to run all commands (`uv run pyright`, `uv run ruff check`, `uv run pytest`, `uv run python -m viterbo.experiments.hello.stage_hello --config config/hello/hello.json`).
<!-- Maybe add the baseline `uv sync --all-extras` or equivalent install step; clarify whether `.venv` is auto-created by prep script. Also mention where lockfiles live and if agents may edit them. -->

## Conventions
- Experiments consume and produce artifacts and json files in `packages/python_viterbo/{data/,config/}` that are committed to git and git LFS.
<!-- Suggest adding a tiny README template per experiment folder (inputs/outputs, entrypoints, tests) so agents can onboard locally without reading this whole conventions block. Maybe add a script to scaffold new experiments with that README + config/data subdirs. -->
<!--J I suggest to just move the conventions about data into its own agent_docs/ ? -->
- <!-- Note on data/LFS: remind agents to keep generated artifacts small and in LFS where applicable; clarify which directories are safe to clean vs must-keep for reproducibility. -->
<!--J that's a reminder about a common best practice that agents already follow; really, really not worth the 1 instruction budget cost -->
- E2E tests sanity check experiment outputs and experiment behavior on small inputs.
- Unit tests for mathematical helper functions to catch bugs and regressions early.
- Docstrings/comments explain the "why" behind design decisions and the "contract" of public APIs.
- Layout: `data/<producer>/` for artifacts, `config/<consumer>/<stage_variant>.json` for experiment config json files, `src/viterbo/experiments/<experiment>/stage_<name>.py` for entrypoints, `src/viterbo/experiments/<experiment>/<other>.py` for helper code that can be imported by other experiments.
- Experiments are run as `uv run python -m viterbo.experiments.<experiment>.stage_<name> --config <path/to/json_file>`.
<!-- Script vs bare commands: prefer popular native commands when simple (`uv run ruff check .`, `uv run pytest`); add thin, well-named wrappers (`lint.sh`, `test.sh`) only when they hide multi-step/brittle sequences. If a wrapper exists, document it as factual context in agent_docs with example invocations, but rely on discoverability via ls scripts/ and --help. Also clarify where logs/metrics are stored and how to clean artifacts between runs. -->
<!--J Since we have multiple dev commands that are run in sequence usually, probably lint.sh is worth it for python for test indeed we may want "uv run pytest <args>" since usually the agent has to specify what tests to run, since running all tests is too expensive for python's data set creation stuff -->
- Use basic type hints to catch bugs early with `uv run pyright`.
- Docstrings document shapes and dtypes and conventions of numpy/pytorch tensors where applicable.
- Use `uv run ruff check --fix .` to autoformat and fix simple linter errors.
- Use `uv run pytest <args>` to run a selection of relevant tests.
- Avoid code reuse between experiments, experiments rarely are stable enough to justify abstracting common code.
- Focus on quick iteration, e2e tests to catch regressions and confirm contracts of artifacts and configs, and unit tests for mathematical helper functions to catch bugs early.
- Reference the thesis writeup where applicable for mathematics, and for experiment motivation and interpretation.
- Keep all configuration in the json files instead of custom command args, so that git tracks the reproducible experiment setups.
<!-- Tension: "avoid code reuse" vs maintainability of shared math utilities. Maybe declare a small `viterbo.common` area for vetted helpers to avoid copy/paste bugs; define criteria for graduating helpers there. -->
<!--J agreed -->
<!-- Could also add "migration policy": when an experiment stabilizes, move shared helpers into common; otherwise keep per-experiment to avoid premature abstraction. -->
<!--J agreed -->

<!-- source: agent_docs/develop-rust.md -->
# Developing in Rust
<!-- Rust onboarding: Add a minimal quickstart (prep script, cd, cargo fmt/clippy/test) and clarify whether to run in repo root or crate root. Also note policy on MSRV/toolchain bumps to avoid accidental updates. -->
<!--J imo doesn't add any value? agents know how to run stuff for rust, they know to run in the rust_viterbo/ folder; so this wastes an instruction budget unit for no gain -->
- Package: `packages/rust_viterbo`
- Goal: High-performance symplectic geometry primitives and algorithms; expose stable bindings for Python via the `ffi` crate.
- Toolchain: Rust 1.91.1 (cargo 1.91.1), sccache installed in the devcontainer.
- Caching: Shared target dir at `/workspaces/worktrees/shared/target` to reduce rebuild times.
- Commands: `cargo fmt`, `cargo clippy --workspace --all-targets`, `cargo test --workspace`.
<!-- Could add an FFI-focused flow (maturin develop / building wheels) so Python users know how to consume the Rust bindings. Also mention workspace features/default-features expectations. -->
<!--J yeah definitely need an onboarding file to disclose info about the ffi only to agents who care -->
- Creates: `geom` crate with core geometry (nalgebra-based vectors); `algorithm` with placeholder algorithms; `ffi` crate with Python FFI bindings (PyO3).
<!-- Add note on MSRV/toolchain pin policy and who bumps it; prevents accidental updates. Also mention where to run commands (repo root vs crate root) to avoid path confusion. -->

## Conventions
- Prefer straightforward, idiomatic Rust solutions over clever or complex ones.
- Use Rust's module system to organize code; keep related functionality together.
- Use types and functions similar to the thesis writeup where applicable, and document differences in code comments.
- Write unit tests to catch bugs and regressions early. Cover happy paths, edge cases, and error paths. Use fixture data where applicable.
- Use analysis tools: `cargo clippy`, `cargo fmt`, `cargo check`, `cargo test`, etc.
- Document the "why" behind design decisions in code comments and docstrings.
- Write in a mathy functional programming style with immutable data structures where sensible; avoid unnecessary mutability.
<!-- Potential contradiction: "straightforward" + "mathy functional" may pull in opposite directions. Maybe articulate the priority (clarity > functional purity) and provide examples. -->
- Only optimize code for performance after benchmarking, profiling, identifying the hotspots, and discussing with the project owner.
- Use the `ffi` crate to expose stable, ergonomic Python bindings. Python uses `maturin` to build the bindings. 
- Use `nalgebra` for linear algebra operations.
<!-- Consider adding a tiny FFI smoke test command (e.g., `uv run maturin develop && uv run pytest tests/test_ffi_smoke.py`) so Python users can validate bindings quickly. -->
<!--J agreed the ffi test is valuable -->

<!--J I skipped over the next file -->

<!-- source: agent_docs/maintain-environment.md -->
# Maintain Environment (extended reference)
<!-- This section is reference-heavy. Maybe split into "quick diagnosis" cheatsheet (common failures + fixes) and a deeper reference. Also include a one-liner about where to report env issues to avoid silent drift. -->

Purpose
- Single reproducible devcontainer; no ad‑hoc local installs. Everything lives in `.devcontainer/*`, `scripts/devcontainer-post-create.sh`, `scripts/worktree-prepare.sh`, `msc-viterbo.code-workspace`.

Base image
- `mcr.microsoft.com/devcontainers/base:ubuntu` with Rust, Python+uv, Lean, Node, TeX Live + latexml, and common CLIs baked in.
- Small extras baked in: `inotifywait` (`inotify-tools`), `entr`, `code-tunnel`.
<!-- Clarify which Ubuntu tag (e.g., 22.04/24.04) and whether we pin by digest. Add a "how to update base image" SOP to keep versions in sync with toolchain pins elsewhere. -->

Host binds (see `devcontainer.json`)
- uv cache, sccache, TeX Live user caches, npm cache/prefix, gh config, worktrees under `/workspaces/worktrees`. These host dirs should already exist; if a mount is missing, create it on the host and rebuild.
<!-- Pain point: Missing mounts cause subtle cache failures. Provide a quick verification command (maybe `scripts/check-mounts.sh`) that agents run once; reduces instructions and confusion. -->
<!-- Also note which mounts are safe to wipe (e.g., caches) vs must-keep (worktrees); prevents accidental data loss. -->

Post-create
- Installs Codex CLI, warms TeX formats. VS Code tunnel is already in the image. No ar5ivist/HTML Docker flow is used.
<!-- Maybe add "where to look if post-create failed" (log path) and a rerun command. Helps agents recover faster. -->
<!-- Good place to remind agents: avoid ad-hoc apt-get/pip installs; change devcontainer/Dockerfile + post-create scripts instead. This keeps environments reproducible. -->

Worktrees
- After `git worktree add <path> <branch>`, run `scripts/worktree-prepare.sh <path>` once. It syncs uv deps for python_viterbo, links Lean caches, and fetches Rust deps into the shared target.
<!-- Clarify whether prep is idempotent and safe to rerun; if not, add a flag. Could also have the script print what it skipped/did for transparency. -->
<!-- Script hygiene: keep these wrappers POSIX-sh, echo commands they run, fail fast (`set -euo pipefail`), and accept `--help` with examples. This lowers the "custom script" tax and makes them easy to audit by agents. -->

Shared caches (per tools)
- Rust: target at `/workspaces/worktrees/shared/target`; sccache at `/home/vscode/.cache/sccache` (bind-mounted).
- Lean: `/workspaces/worktrees/shared/lean/{packages,build-global}` via symlinks created by the prep script.
- Python: uv cache bind-mounted at `/home/vscode/.cache/uv`; per-worktree `.venv` under `packages/python_viterbo/`.
- Node: npm cache/prefix `/home/vscode/.cache/npm`, `/home/vscode/.local` (set in post-create).
- TeX Live: user caches `/home/vscode/.texlive2023`, `.texmf-var`, `.texmf-config`; remove only if corrupted.
<!-- Add disk-usage guidance and cleanup commands (safe vs unsafe). Shared caches can silently bloat; having thresholds or a periodic cleanup cadence would help. -->

LaTeX builds
- Local `latexmk`/`latexmlc`; no Docker socket required.
<!-- Could add "typical dev loop" example (edit -> lint -> build --draft) and expected build time. Also specify where PDFs/HTML land so agents can open them quickly. -->
<!-- Maybe add a pointer on handling heavy TeX caches (when to nuke ~/.texlive2023) and how to reinstall the minimal set if corrupted. -->

<!-- source: agent_docs/write-agent_docs.md -->
# Writing Agent Docs
<!-- Opportunity: Add a lightweight template (section order + checklist) to keep docs concise and discoverable, without per-file front-matter. Also document how to regenerate any aggregated snapshot (if kept) to prevent drift. -->
<!--J okay a template file / template code block as part of the file may be useful -->
- Goal: Provide onboarding and reference docs for agents working on the project. Write in a way that is maximally helpful for agents.
- Onboarding knowledge goes into `agent_docs/` and `AGENTS.md`.
- Documentation and thesis writeup are also used for onboarding and follow similar principles. See `write-latex.md` for style guidance.

<!-- Script docs best practice: mention wrappers as examples (name, purpose, common args, sample call/output) but keep imperatives minimal; rely on discoverability via ls scripts/ and --help. Use common names (lint.sh, test.sh, build.sh, bench.sh, prep-worktree.sh) to reduce "custom" tax. -->
<!--J yep, we need a agent docs for best practices for writing scripts -->

- Agents have zero prior context about the project, but are already familiar with all popular toolchains, frameworks, patterns and domain knowledge.
- Instead of explaining such familiar concepts, we just need to tell the agent which ones we are using when there are multiple popular options.
- We also name-drop familiar concepts to help the agent consider them as available options, IF agents demonstrate the need for such reminders.
- We have to introduce custom concepts, code architecture, and custom math domain knowledge from scratch for each agent. That is why we prepare high quality onboarding docs in `agent_docs/` and provide docstrings and comments in code next to the relevant code. The colocation helps agents find the relevant docs precisely when they need them.

- Agents use command line tools and text files; no IDE, no interactive GUIs; they can view image files, so plots and diagrams are possible.
- Agents read files and command output in one go without pause, so it is important to use digestible, clear, unambiguous language with low cognitive overhead.
- Agents don't have the time to cross-check every single claim in the repo; we must ensure that all claims are kept up to date and are literally correct and unambiguous to rule out misunderstandings.
<!-- Maybe keep a short "doc health" checklist (must/should separation, links to scripts, cross-links updated) to run before merging doc changes. Could live in the PR template for doc edits. -->
<!--J not sure what you mean with "to run" but yeah, we can phrase the instructions more clearly and more distinctly as a checklist format and remind agents to check if best practices are satisfied -->

- Agents can draft and edit these docs, but the project owner reviews and must approve any changes to `AGENTS.md` or `agent_docs/` (policy, expectations, onboarding); treat these files as high-cost.

- Agents can report about the frictions they experience while working on the project, including with onboarding docs, with environment setup, with toolchain usage, or with current code or documentations or thesis writeup.
- Agents are less experienced in suggesting the best improvements and tradeoffs between different setups. Instead the project owner has to make the final call, and agents merely point out issues, provide feedback and propose multiple solutions.
- We should collect such feedback, and iteratively improve the repository and project conventions.

<!-- source: agent_docs/write-gh-issues-prs.md -->
## Writing GitHub Issues and PRs
<!-- Consider adding issue/PR templates that encode the bullets (required readings, must-haves vs suggestions, footer) so agents don't have to recall them. Also define expected size/scope for issues to avoid cognitive overload. -->
<!--J agreed, a template would be more natural for conveying e.g. the footer rule than writing instructions explicitly here. then we can just mention where the template is, and agents know what to do themselves -->
- Goal: Write GitHub issues and PRs that agents understand and find actionable.
- Use GitHub CLI with `--body-file` to avoid shell quoting pain.
- Always include a footer `Written-by: codex agent running in worktree <path>`
- Relevant context:
  - Agents have zero prior context about the project. They go through onboarding docs in `agent_docs/` and `AGENTS.md` and can read up on anything they need from the repo.
- In consequence, issues and PRs must help agents onboard quickly for the described task / for the implied review task.
  - We mention the files that are required reading for the task, or that may be potentially useful further readings. This reduces the chance that agents miss important context.
  - We put important context preferably into files in the repo, but can also put it into the issue/PR body if it is only short-lived context (e.g. for the task itself) or if it will be written into files per the task goals (e.g. if a code spec as context then turns into committed code).
  - We avoid overwhelming agents with tasks that require a large amount of reading files, reading command output, and editing files. Instead we break down such large tasks into more focused milestones, so that each agent in the sequence has to read and edit only a manageable amount of not-too-distinct content.
  <!-- Maybe introduce a "time-to-read" heuristic (e.g., keep required reading under N lines) and a standard table summarizing required files with 1-line purpose, to make issues scannable. -->
  <!--J no clear heuristic exists, sorry. -->
  - We ensure literal correctness and unambiguity in issue and PR descriptions, to avoid misunderstandings. Agents do not have the context we have, so they cannot resolve misunderstandings or detect incorrect claims in the text themselves.
  - We write in a clear, digestable style with low cognitive overhead, to help agents process the information quickly and correctly. 
  - We clearly distinguish between must-have goals, and mere suggestions for how to achieve them, to avoid agents getting stuck on non-essential details, or worse, trading true goals against irrelevant ideas.
- Most PRs are reviewed by the project owner only. The project owner will read fewer files than agents do, and will focus on the git diffs of the changes, and verify high-level claims made by the agent about the delivered branch. To make this job easier, we ensure that PR descriptions restate the changes from a high-level perspective as an overview, and then describe also the agent's process of arriving at the changes, so that the project owner is aware of what commands and files were consulted along the way.
- Agents can use `--body-file` also as a chance to iterate on their drafts before submitting them.
- All agents share the GitHub identity of the project owner, thus various fields in PRs and issues lose their meaning (e.g. author, assignee). Instead we use footers and body text to clarify these aspects where relevant.
<!-- Could capture the expected PR outline (Problem, Changes, Tests, Risks, Follow-ups, Required reading) in a template file to reduce memory load and make reviews faster. -->
<!-- Add explicit pointer to .github/ISSUE_TEMPLATE/ and PULL_REQUEST_TEMPLATE.md locations so agents find the defaults instead of memorizing. -->

<!-- source: agent_docs/write-latex.md -->
# Writing the Thesis (LaTeX)
<!-- Consider a "thesis quickstart" snippet (lint/build/serve commands) plus a link to a style cheatsheet. If HTML/PDF outputs are in CI, add a link pattern so agents can preview without building. -->
<!--J mentioning scripts/{lint.sh, build.sh,serve.sh} is enough; a style cheatsheet would be good if agents had style problems, but I think just saying "follow best practices as recommended by ArXiV" will tell agents all they need to know; they were trained on ArXiV papers after all, and know the style very well. -->

- Goal: Write a professional-level master's thesis in mathematics.
- Target audience: interested mathematicians with a background in symplectic geometry, but not necessarily any background in polytopes or Viterbo's conjecture, and no background in modern software engineering.
- The thesis must be self-contained. References to other parts of the repo are treated as non-essential further readings.
- Sources/output: LaTeX lives in `packages/latex_viterbo/`. PDF is primary; HTML is generated via `latexmlc`.

## Writing Style
The style we aim for is
- Literally correct and unambiguous. We are mathematically precise in what we do, to transfer deep understanding to the reader.
- Explicit, low cognitive overhead, complete, skimmable. A reader who reads top to bottom should understand everything, using the usual ability to fill small gaps in natural language mathematical writing that is expected of professional mathematicians. We are actually leaning towards being very explicit and detailed, but structure our writing so that a reader can skip over details if they are faster at inferring them than reading them. In particular we clearly put proofs of statements into proof environments, so that a reader can skip them if they already believe the statement and are not interested in the proof strategy or proof details right now.
- Motivated. We explain the "why" and "generating ideas" behind definitions, theorems, proofs. Often there is a simple empirical reason that some definition covers more cases of interest than another, or that some definition is excluding edge cases that are different in a bothersome way but not relevant. Sometimes there are good reasons though for why some definition is natural, i.e. splits reality at the joints and is expected to match other natural definitions and theorems well.
- Structured. We help the reader navigate and skim the document by using clear headings, announce (spoiler) the takeaways early, and signpost the flow of the document well.
- Consistent notation. We pick notation that is similar to existing literature where possible, and consistent throughout the document. We often note when referenced documents deviate from our notation, so that readers who jump to those documents can translate easily in their heads.
- Clear distinction between mainline text and asides. We use admonitions and footnotes and references to appendices / optional sections.
<!-- Might add a short example snippet showing preferred structure (statement + sketch + proof) to ground the style guidelines. Also, clarify expectations around notation drift vs literature and how to record deviations. -->
<!--J probably enough to have existing latex code that agents read + imitate -->

## Toolchain
- TeX Live (Ubuntu 24.04 packages ~TL2023), with latexml to create HTML output.
- Lint: `packages/latex_viterbo/scripts/lint.sh` (chktex + draft compile + latexml sanity).
- Build: `packages/latex_viterbo/scripts/build.sh [--production] [--pdf-only] [--html-only]` (draft to `build/`, production to `dist/`).
- Local serve: `packages/latex_viterbo/scripts/serve.sh [--production] [--watch] [--port 8000]` (serves draft/production HTML+PDF).
- CI: `.github/workflows/gh-pages.yml` builds and publishes artifacts on push to `main`.
<!-- Could mention expected runtime and RAM for lint/build to set agent expectations. Also specify where generated assets live (dist/build paths already noted) and cleaning commands. -->
<!--J uff, that's pretty detailed, not sure if agents profit from that kind of knowledge or if it distracts them? The agents can discover the (standard location) artifacts themselves. We can add a clean.sh if needed -->

## LaTeX Conventions and Syntax Reminders
- Follow best practices from ArXiv and standard LaTeX style guides.
- Math: `\(...\)` for inline, `\[...\]` for display; Avoid dollar signs since they cause shell escaping trouble for agents who edit files.
- Proofs: wrap proofs in the `proof` environment.
- Figures/tables: python pipelines store generated assets in `packages/latex_viterbo/assets/`.
- Chapters: Create a `includeonly.tex` (git-ignored) to control which chapters are included during draft builds.
- Bibliography: use `references.bib`.
- Packages/macros/styles: stick to well-known best-practice code snippets and packages; KISS, YAGNI.
<!-- Add a note on where to put new macros/environments (e.g., preamble vs per-chapter) and a policy for naming to avoid clashes. Also whether to use arXiv-friendly packages only. -->
<!--J We can just add a preamble.tex and agents will know by heart to put content there. Good point though, we really should have a preamble.tex -->

<!-- ================= Proposed Repo / Doc Layout (for discussion) =================

Context: onboarding.md is a scratchpad; final sources should be small per-package docs plus a minimal root AGENTS. Any aggregated view is optional and generated from those sources.

Goals: minimize instruction load; co-locate docs with code; clear breadcrumbs.

Top level
- AGENTS.md (10–15 line start-here + repo map + links to per-package AGENTS; no package specifics)
- agent_docs/ (cross-cutting only): maintain-environment.md; develop-devops-scripts.md; write-agent-docs.md; write-gh-issues-prs.md; add-git-worktree.md; modify-environment.md
- Optional helper: scripts/gen-onboarding.sh to produce a review snapshot that concatenates root + per-package AGENTS; per-package files remain canonical.

Per package (example: packages/rust_viterbo)
- packages/rust_viterbo/AGENTS.md (when to open Rust, quickstart commands, cache note, link to agent_docs)
- packages/rust_viterbo/agent_docs/
  - develop-library-code.md
  - folder-layout.md
  - python-ffi-with-pyo3-maturin.md
  - benchmark-the-library.md

Similarly:
- packages/python_viterbo/AGENTS.md + agent_docs/{develop-experiments.md, folder-layout.md, use-rust-ffi.md, scaffold-new-experiment.md}
- packages/lean_viterbo/AGENTS.md + agent_docs/{develop-proofs.md, lemma-search-cheatsheet.md, folder-layout.md}
- packages/latex_viterbo/AGENTS.md + agent_docs/{build-and-serve.md, style-guide.md, assets-and-figures.md}
- packages/thesis/ is in migration; plan to delete once latex_viterbo fully replaces it.

Supporting conventions
- Skip per-file front-matter; git history covers dates, and onboarding ownership is universally the project owner. Keep docs short and scoped by subtask.
- CODEOWNERS guards AGENTS.md and agent_docs/**.
- Issue/PR templates bake in footers and required-reading sections so fewer imperative instructions are needed.

Migration path
1) Remove packages/thesis/ when safe; stop linking to it.
2) Create per-package AGENTS + agent_docs skeletons (even 5–10 lines) with quickstart and pointers.
3) Move existing package-specific content from root agent_docs into package folders; prune root to cross-cutting topics.
4) Optionally add the generator script + README note; otherwise keep aggregated views ad hoc for reviews only.

Alternatives
- Skip generator; instead provide a tiny script (shell) that prints the relevant doc list (no concatenation), keeping sources single-location.
- Longer-term: render agent_docs via mkdocs for search/browsing, but keep AGENTS minimal and textual for CLI agents.

-->

<!--J
My suggestion for a concrete layout and what ought to mentioned. Don't treat this as a final decision, just a first idea. I am quite sure I forgot entire files and points in many files or included points that are better moved elsewhere or dropped.

- AGENTS.md
  * it's a monorepo, it's a math thesis project, we use onboarding docs, pls read them, run hello.sh, you may be in a worktree and that's okay, there's a single environment we use and that is fully defined over there
- agent_docs/
  - maintain-environment.md
    * files, design principles, must alert project owner to exact changes, only project owner can rebuild devcontainer, should ofc not install stuff ad-hoc but edit environment and rebuild instead
  - write-agent-docs.md
    * purpose of agent onboarding material, design principles, writing style, when to write / edit / delete docs or text therein, detailed project owner approval needed, template for writing agent docs
  - write-gh-issues-prs.md
    * purpose of issues/PRs, link to template, mention --body-file rule for gh cli, mention ideal task size; lots of convnetions are now instead in the template so no need to repeat them here
  - add-git-worktree.md
    * purpose of worktrees, how to create them with script, when and how to remove them, mention shared caches as a design concept

- packages/rust_viterbo/
  - AGENTS.md
    * this is a high performance math library with python ffi, there's crates geom+algorithm+ffi, further reading: agent_docs/
  - agent_docs/
    - develop-library-code.md
      * toolchain, deps, commands reminder, code conventions (nalgebra, functional programming style, docstrings, unit tests), when to optimize and when to expose to ffi
    - python-ffi-with-pyo3-maturin.md
      * when to expose to ffi (redundant, yes, but some agents may only care about this file and not develop-library-code.md), toolchain, code conventions, commands (including the python tests!), troubleshooting tips
    - benchmark-the-library.md
      * when to benchmark (redundant), toolchain, commands, how to interpret results, how to optimize based on results, premature optimization warning, how to profile, code conventions (ablation studies + a debug version with lots of toggles)

- packages/python_viterbo/
  - AGENTS.md
    * this is the orchestration layer for experiments, we use uv, there's folders for src & e2e tests & data & config, further reading: agent_docs/
  - agent_docs/
    - develop-python-code.md
      * toolchain, commands reminder, code conventions, layout conventions, when to write unit tests vs e2e tests, docstring conventions, mention an example experiment that has copyable code structure with best conventions already applied, explain why to avoid code reuse between experiments
    - use-rust-ffi.md
      * just points to packages/rust_viterbo/agent_docs/python-ffi-with-pyo3-maturin.md since it's the same info and we don't want to duplicate
    - experiments-data-and-config.md
      * where goes what, how to run an experiment stage, how to write config jsons, how to write/read data artifacts from code, how to keep things reproducible
    - creating-plots-and-tables.md
      * how to create stages that turn data into plots/tables for the thesis, where the thesis assets go, and what code style & output style conventions to follow
  
- packages/lean_viterbo/
  - DELETE THIS PACKAGE AND REMOVE ALL REFERENCES!
  - turned out Lean4 just isn't good enough for what we do :/
  - so we will not do Lean4; we can keep the entire setup in the git history, so if necessary we can resurrect it in the future; but that's sth the project owner can decide, so no need to tell agents during onboarding that Lean4 ever existed

- packages/thesis/
  - WILL BE DELETED ONCE latex_viterbo IS FULLY READY
  - let's already eagerly remove all references to it, so we don't forget later
  - we can keep a single reference in AGENTS.md that explains that packages/thesis/ is deprecated and in-migration, and will be deleted once packages/latex_viterbo/ is fully ready

- packages/latex_viterbo/
  - AGENTS.md
    * this is where the latex thesis lives, we use tex live + latexml for pdf + html output, we follow best practices from arxiv, further reading: agent_docs/; no need to mention files that are gonna be discovered instantly (bibliography.bib)
  - agent_docs/
    - latex-style.md
      * we use ArXiV best practices, no dollars due to bash escaping friction, proof environment
    - thesis-writing-style.md
      * target audience, the quality goals (mathematically correct, complete reference for our work, treat code repo as optional further reading, motivated and structured writing, consistent notation), workflow for meeting the quality goals (stay close to already vetted writing, wrap in \edit{} for text that needs project owner review, fix typos on your own without seeking permission, etc)
    - assets.md
      * ref the assets location, ref to creating-plots-tables.md in python_viterbo, convention: python owns assets generation, latex just includes them
    - build-and-serve.md
      * toolchain, commands reminder, mention lint/build/serve scripts as convenience wrappers, mention expected runtimes and where artifacts go, the includeonly.tex trick for faster draft builds (i suggest we add a includeonly.tex.example file as a template for agents to copy while indeed keeping it git-ignored so worktrees don't tell the main branch to build only parts of the thesis)

- .github/
  - ISSUE_TEMPLATE/
    - template.md
      * showcases proper title, structuring, reading list at the end, footer with Written-by, must-have vs suggestions, etc
  - PULL_REQUEST_TEMPLATE.md
      * similar to template.md but adapted for PRs

- packages/python_viterbo/
  - src/viterbo/experiments/template/
    * a template experiment that can be copied + adapted for new experiments, showcasing best practices in code structure, config jsons, data artifacts, tests, docstrings, etc
  - data/template/{test/hello.parquet,production/hello.parquet}
  - config/template/{test.json,production.json}

- scripts/
  - hello.sh
    * prints commands + dynamic information about the repo; concretely: 
      - pwd
      - git status -sb
      - {unsure how to do but print a partial folder tree, clearly mark omissions so agents don't get confused and think files are missing}
      - {unsure if a good idea: run all lint/test commands and print summary output to assess health; i think it's better not to do this, and let agents run the commands intentionally}
  - worktree-new.sh
    * replaces worktree-prepare & git worktree add; creates worktree + runs prep script + does safety checks e.g. whether origin/main == main, whether uncommitted changes exist, etc
  - worktree-remove.sh
    * safely removes a worktree, warns and requires [--force] if e.g. uncommitted changes exist or worktree's branch wasn't merged into main yet, or if origin/main != main etc.

- packages/*/scripts/
  * depends on the package, but we use standard names whenever the workflow isn't just a single popular command (e.g. for python we wouldn't have a test.sh bc we want agents to run `uv run pytest <args>` with carefully chosen args; but for latex we do want a lint.sh since agents may not be used to our custom linting setup)
  - rust: we mostly use popular commands
    - cargo clippy
    - cargo fmt
    - cargo test
    - cargo build
    - cargo bench (iirc?)
  - python:
    - lint.sh (ruff, ruff check, pyright)
    - uv run pytest <args> (no wrapper, since args vary per agent's situation)
    - uv run python -m viterbo.experiments.<experiment>.stage_<name> --config <path/to/json_file> (no wrapper, since args vary per experiment)
  - latex:
    - lint.sh (chktex + draft build + latexml sanity)
    - build.sh [--production] [--pdf-only] [--html-only]
    - serve.sh [--production] [--watch] [--port 8000]

- packages/latex_viterbo/
  - preamble.tex
    * all custom macros/environments/styles go here, so agents know where to put new ones
  - includeonly.tex.example
    * example template for includeonly.tex that agents can copy to includeonly.tex for faster draft builds; git-ignored includeonly.tex but not .example, so worktrees don't affect main branch builds
  
================= End Proposed Repo / Doc Layout =================

-->