# Process – Issues, Autonomy, Quality, Reproducibility

This document explains how work on the project is organised: how we use issues, how agents are expected to work autonomously, and what quality and reproducibility mean here.

## Issue-driven development

- All work is tracked with **GitHub issues**. Use `gh issue list` to discover work, `gh issue view <number>` to gather context, and `gh issue status` to see what is already assigned to your current branch.
- Create new issues with `gh issue create --body-file path/to/draft.md`. Writing the body to a file avoids shell escaping mistakes and keeps long-form Markdown under version control if helpful.
- The devcontainer is authenticated as the project owner; do **not** touch the GitHub owner/assignee fields. Instead, state which agent/worktree is handling the task inside the issue body or comments.
- Keep issue text high-signal: include acceptance criteria, reproduction steps, links to experiments, and clear "Definition of Done" checklists. Attach screenshots or logs via `gh issue comment --body-file ...` when debugging.
- Follow well-known GitHub hygiene:
  - Titles summarise the user-visible outcome.
  - Labels communicate priority/kind.
  - Comments stay concise and actionable (status → blockers → next actions).
  - Closing keywords (`Fixes #123`) go in PR descriptions when ready.

Lifecycle overview:
- Jörn drafts the highest-level issue(s) outlining desired outcomes.
- An agent turns that issue into a concrete plan (either by editing the top comment or adding a clarifying comment with checklists).
- Implementation happens on one or more worktrees; progress is reported back to the issue via `gh issue comment`.
- When the implementation meets the acceptance criteria, the agent opens a PR and links it to the issue. Jörn reviews and ultimately merges or rejects it.

### Pull requests

- Use `gh pr create --base main --head <branch> --title "..." --body-file path/to/summary.md`.
- Every PR body should include:
  - a short problem + solution summary,
  - validation notes (tests, linters, manual verification),
  - follow-up work if scope was cut.
- Reference the relevant issues (for example `Closes #42`) and keep titles consistent with the associated issue.
- Only the project owner merges into `main`. Agents push commits, respond to review, and mark PRs ready, but leave `gh pr merge` to Jörn.
- Rebase/merge conflicts are resolved locally within the worktree before updating the PR.

## Autonomy and worktrees

- There is one canonical git clone, one devcontainer, and many git worktrees.
- Worktrees live under a bind-mounted directory such as `/var/tmp/msc-viterbo/worktrees` and are exposed inside the devcontainer via `/workspaces/worktrees`.
- Each worktree directory name is usually:
  - the primary GitHub issue slug/number (for single-issue branches), or
  - a short slug summarising a group of related tasks.
- Branch names typically follow the pattern `agentx/{worktree-name}`.
  - Example: GitHub issue `#18 fix README typos` maps to worktree `/workspaces/worktrees/issue-0018-fix-typos-in-readme` on branch `agentx/issue-0018-fix-typos-in-readme`.
- These naming conventions are **recommended**, not enforced; they must remain valid as filenames, folder names, and branch names.
- Use `scripts/provision-worktree.sh <worktree-name>` to create a new worktree and branch from `main` (or `origin/main`).

Autonomy policy:
- For any well-defined issue, an agent should:
  - understand the spec,
  - devise a plan,
  - implement and test locally,
  - summarise and open a PR.
- Only escalate to Jörn for:
  - ambiguities or contradictions in specs,
  - missing domain knowledge that cannot be inferred from existing docs/code,
  - repeated failures where further autonomous attempts are unlikely to help.
- Multiple agents may work on copies of the same issue (e.g. separate worktrees) in parallel; Jörn chooses the best resulting PR.

## Quality standards

We aim for high quality throughout, because many different AI agents will touch the codebase over time.

- **Code quality:** simple, boring, readable, and maintainable code is best.
- **Correctness:** code must not make false claims.
  - Failing tests must be clearly labelled as expected failures when intentional.
  - Known bugs and outstanding tasks must be reflected in both the issue tracker and the code (TODOs, comments).
- **Reliability:** we use manual review, automated static checks (linters, type checkers), and automated runtime checks (unit tests, property-based tests, end-to-end tests).
  - We also run benchmarks where relevant to track performance and resource usage over time.
- **Documentation:** code should contain enough comments and docstrings to:
  - avoid forcing future agents to re-derive non-obvious implications,
  - record rationales behind non-trivial design decisions and bug fixes.
  - We colocate docs with code whenever reasonable.
- **Onboarding:** we keep `AGENTS.md` files up to date at the root and package levels, and reference further, more detailed docs only when needed.
- **Ergonomics:** we prefer standard tooling and workflows, and incorporate agent feedback to reduce friction.

Package-level `AGENTS.md` files define canonical commands and quality targets (for example, which test suites must be green). Prefer standard ecosystem commands like `cargo test`, `uv run --extra dev pytest`, and `lake build`.

## Reproducibility and tags

We design the project for full reproducibility from scratch whenever feasible:

- Anyone who clones the repo and opens the devcontainer should be able to build, test, benchmark, and run all code, tools, and data pipelines from scratch, without deep project-specific knowledge.
- However, we do **not** enforce full reproducibility on every commit (not even every commit on `main`); that would slow development too much.
- Instead we continuously push back towards a fully reproducible state.

When we reach such a state:
- We create an **annotated git tag** on the corresponding commit.
- That tag marks a fully reproducible state with a clear, coherent feature set.
- These tags are the preferred entry points for reproducing the thesis and its results.

Reproducibility checklist (at a tagged state):
- The devcontainer fully defines the development environment.
- Package toolchains are fully defined in their setup files and scripts.
- Code can be built, linted, type-checked, tested, and benchmarked from scratch successfully.
- The code achieves a coherent working feature set.
- Code comments and other documentation accurately describe the current commit state.
- Onboarding docs describe current workflows and expectations correctly.
- Data artifacts can be deleted and re-generated via documented or automated pipelines.
