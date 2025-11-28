# Context Engineering for Agents

Goal: make new context maximally useful and safe for agents (and future refactors) with minimal bloat.

What to add / not to add
- Add: distilled rules, decisions, templates, verified claims, and dense examples showing the chosen style. Prefer canonical sources (TeX, code, data) over paraphrase.
- Avoid: PDFs as a primary source for formulas (copy TeX from arXiv sources instead), open-ended brainstorms without labels, and duplicated guidance already present in package docs.
- Mark uncertainty explicitly (`TODO`, `(?)`, or `<proposed>`). Flag internal-only material with `internal: true` front matter when in MDX.

Placement rules
- Cross-package or tooling-agnostic guidance → `docs/` (this folder).
- Package- or toolchain-specific guidance → `packages/<pkg>/docs/`.
- Thesis prose (public) → `packages/thesis/src/`; drafts/internal → `packages/thesis/src/internal/`.
- Legacy/reference only → `packages/thesis/archive/` (read-only).

Style and format
- Default to MDX with front matter for thesis-facing material; plain MD is fine for short meta files like this one.
- Write literally and explicitly; avoid GitHub-summary voice. Use short declarative sentences; examples can be dense and name-drop well-known texts instead of teaching basics.
- Link to sources by path; avoid URLs unless necessary. Use TeX snippets from sources, not PDF copy/paste.

Process and maintenance
- When adding context: state scope and intended consumers, include a minimal example, and note expected shelf life if temporary.
- Keep files single-purpose; split if a file grows beyond one topic.
- Request project-owner review for new context files or major rewrites; note in the PR/commit that review is needed if not yet obtained.
- When conventions change, update the canonical file and remove/redirect superseded snippets rather than leaving both versions.
