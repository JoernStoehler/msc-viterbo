# AGENTS – Thesis Package

You are in `packages/thesis/`, which contains the sources and build pipeline for the written MSc thesis **"Probing Viterbo's Conjecture"**.

## Strategy

**Read these first (required):**
- Root `docs/context-engineering.md` — cross-package context rules.

- Canonical sources are `.qmd` files under `src/`, built to static HTML with **Quarto**.
- Roughly a week before submission we will export to LaTeX/PDF; until then, optimize for GH Pages (math + plots) and fast rebuilds.

## Layout (initial)

- `src/` – Markdown sources (public chapters).
- `src/internal/` – drafts/internal notes (kept in nav under “Internal”).
- `src/literature/` – per-paper digests.
- `build/` – generated artifacts (Quarto HTML under `build/site/`, gitignored).
- `archive/` – legacy docs, read-only.

## Required reading & layout pointers

- No YAML front matter; start each file with an `# H1` title.
- Drafts/internal material belongs in `src/internal/`; public chapters in `src/`; literature digests in `src/literature/`.
- Cross-package context rules: `docs/context-engineering.md` (root). Follow its placement/maintenance rules when adding new context.
- Avoid PDFs for math verification; prefer TeX from the arXiv store (`packages/thesis/scripts/arxiv_fetch.sh` places sources under `build/arxiv/`).
- Math input: write math with `\(...\)` and `\[...\]`; prefer TeX commands over Unicode symbols.

## Architecture context

- Every claim in the thesis should reference reproducible artifacts: algorithms from `packages/rust_viterbo`, experiments from `packages/python_viterbo`, proofs from `packages/lean_viterbo`.
- Keep citations to code/lemmas stable by referencing commit hashes or tagged releases when available.
- When the thesis build process changes (e.g. switching from Markdown → LaTeX), document the workflow here so automation agents can follow it without re-reading history.

## Source format & components

- Files live in `src//`. No YAML front matter; start with an `# H1` title.
- Write plain Markdown. For statements use bold labels (`**Definition.**`, `**Proposition.**`); proofs start with `Proof.`.

## Figures and assets

- Numerical experiments live in `packages/python_viterbo/`. Pipelines should emit **both** static PNG/SVG and interactive JSON (Plotly/Vega) per figure ID under `src/assets/figures/<chapter>/<id>.*`.
- Embed in Markdown using the static image, and optionally add a Plotly div for interactivity:
  - `![caption](assets/figures/ch1/fig-foo.png)`
  - `<div data-plot-json="assets/figures/ch1/fig-foo.json"></div>`
  `assets/js/plotly-hydrate.js` (included via mdBook config) fetches the JSON and renders via the global Plotly CDN.
- Always commit static assets. Interactive specs must be reproducible (pin seeds/commits).

## Interaction with `packages/docs-site/`

- `packages/thesis/scripts/build-site.sh` builds static HTML to `build/site/` via Quarto.
- `packages/docs-site/scripts/docs-publish.sh` copies `build/site/` into `packages/docs-site/public/thesis/` (and publishes gh-pages). No direct coupling beyond that copy.

## Export workflows

- **Docs / GH Pages**: `packages/thesis/scripts/build-site.sh` (Quarto) then `packages/docs-site/scripts/docs-publish.sh` (builds all packages and publishes gh-pages).
- **Print / PDF** (future): add `build/pandoc/` and a script that reuses the Markdown sources; swap interactive plots for static assets.

## ArXiv sources (offline access)

- Canonical immutable store (persistent across worktrees/containers): `/workspaces/worktrees/shared/arxiv-store/<id>/vN/` containing `source.tar.gz`, optional PDF, and `.sha256` files. Downloads are chmod a-w after fetch.
- Per-worktree read-only extracts (gitignored): `packages/thesis/build/arxiv/<id>/vN/`. These are re-created from the store; safe to delete/regenerate.
- Fetch script: `ARXIV_STORE=/workspaces/worktrees/shared/arxiv-store packages/thesis/scripts/arxiv_fetch.sh -p <id>vN`. Requires explicit arXiv version (`v1`, `v2`, ...). PDF is optional (`-p`).
- Integrity: script writes and checks SHA256; extraction is read-only to avoid accidental edits.
- Text extraction helper (best-effort): `uv run --with pypdf packages/thesis/scripts/pdf_to_text.py packages/thesis/build/arxiv/<id>/vN/<id>.pdf > notes.txt` for quick grep/labels.

## Tooling and commands

- Build HTML (thesis): `packages/thesis/scripts/build-site.sh` (`quarto render`). Output in `build/site/`.
- Live preview: `packages/thesis/scripts/serve.sh` (`quarto preview --host 0.0.0.0 --port 8000`).
- Math: KaTeX via Quarto. No static lint currently.
- Full publish (all packages → gh-pages): `packages/docs-site/scripts/docs-publish.sh` (fails fast unless SKIP_* set).
- Figures pipeline: extend Python scripts to emit `*.png` + `*.json` into `src/assets/figures/...`.
- PDF export: not yet implemented; keep Markdown math/structure clean for future conversion.
