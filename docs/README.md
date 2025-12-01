# Root Docs (Cross-Package Agent Knowledge)

Purpose: hold project-wide knowledge that applies across packages and toolchains. Package-specific material lives in `packages/*/docs/`; thesis prose lives in `packages/thesis/docs/`.

Contents
- `context-engineering.md` — how to add/maintain agent-facing context.
- Future cross-package notes (e.g., shared data policies, devcontainer quirks). Keep each topic in its own small file.

Conventions
- Write in the same literal, explicit style as the rest of the repo; assume AI agents are the primary readers.
- Prefer pointers into package docs over duplication. If a rule is package-specific, add it there and link to it from here only when necessary.
- Do not store thesis chapters or drafts here; those belong under `packages/thesis/docs/` (public) or `packages/thesis/archive/` (draft/internal).
