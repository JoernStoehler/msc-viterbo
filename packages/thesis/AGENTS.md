# AGENTS – Thesis Package

You are in `packages/thesis/`, which now ships the thesis as **MkDocs + Material** using plain Markdown (MyST not required). Quarto is removed.

## Strategy
- Canonical sources live under `packages/thesis/docs/` (Markdown only). No YAML front matter; start each file with `# Title`.
- Build HTML locally with `make docs-html` (wrapper around `mkdocs build -f packages/thesis/mkdocs.yml`).
- Optional preview: `make docs-serve` (mkdocs serve on :8000).
- Lint math markup: `make docs-lint` (fails on `$...$` and unmatched `\(`/`\)` or `\[`/`\]`).

## Layout
- `docs/` – thesis content; mirrors the old Quarto src tree.
- `docs/assets/` – css/js/figures (static). Interactive Plotly specs stay under `docs/assets/figures/` alongside PNG/SVG.
- `docs/overrides/assets/` – `extra.css` for theorem/definition/proof styling; `mathjax-config.js`.
- `site/` – mkdocs build output (gitignored).
- `archive/` – legacy material; keep Quarto-era files here if you need to reference them.

## Writing conventions
- Math delimiters: use `\(...\)` for inline and `\[...\]` for display. `$...$` is forbidden (lint enforces).
- Statements: use Material admonitions with stable IDs, e.g.
  - `!!! theorem "Theorem (Viterbo bound) {#thm-viterbo}"`
  - `!!! proof "Proof"`
  - `!!! definition "Admissible polytope {#def-admissible-polytope}"`
  References use `[text](#thm-viterbo)`.
- Figures: place generated assets in `docs/assets/figures/<chapter>/`. Link via standard Markdown (`![cap](assets/figures/ch1/foo.png){#fig-foo}`). Keep interactive JSON alongside PNG/SVG; Plotly is loaded via CDN + `assets/js/plotly-hydrate.js`.
- Labels: every theorem/lemma/proposition/definition/proof that needs referencing must carry an explicit `{#id}` in the title. Notes/examples may stay unlabelled.
- Citations: the current stack does not render `[@key]`; leave as plain text or expand manually.

## Commands
- Build: `make docs-html` or `packages/thesis/scripts/build-site.sh`.
- Serve: `make docs-serve` or `packages/thesis/scripts/serve.sh`.
- Lint: `make docs-lint` (runs `scripts/lint_math.py`).
- Prep: `scripts/worktree-prepare.sh --docs` currently prepares `packages/docs-site`; MkDocs needs no extra prep beyond Python tooling already in the devcontainer.

## Interaction with other packages
- Figures/data come from `packages/python_viterbo/`; regenerate figures there and copy outputs into `docs/assets/figures/` with reproducible commands noted in the surrounding text.
- Proof/algorithm references should point to stable commits in `packages/lean_viterbo/` and `packages/rust_viterbo/` when relevant.

## Notes for agents
- Keep the style boring and standard: no bespoke plugins beyond those in `mkdocs.yml` (`search`, `autorefs`, a small set of `pymdownx` extensions, MathJax).
- If you need offline MathJax, vendor it and update `mathjax_path` in `mkdocs.yml`.
- When adding new pages, update `mkdocs.yml` nav immediately to avoid orphan warnings.
