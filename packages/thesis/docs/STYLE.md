# Thesis Style Guide

- **Math delimiters**: use `\(...\)` for inline and `\[...\]` for display. Do not use dollar-delimited math.
- **Statements**: use Material admonitions with explicit IDs.
  - `!!! theorem "Theorem (Name) {#thm-name}"`
  - `!!! proposition "Proposition (Name) {#prop-name}"`
  - `!!! definition "Definition (Name) {#def-name}"`
  - `!!! proof "Proof"`
  Link via `[text](#thm-name)`; never cite bare numbers.
- **Figures**: place under `assets/figures/<chapter>/`; reference with `![caption](assets/figures/chX/foo.png){#fig-foo}`. Keep interactive JSON next to the static image when needed.
- **Sections/nav**: every new page must be added to `mkdocs.yml` nav immediately to avoid orphans.
- **Lint**: run `make docs-lint` before committing; it fails on raw dollar math and unmatched `\(`/`\)` / `\[`/`\]` counts.
- **Build/serve**: `make docs-html` for a clean build, `make docs-serve` for local preview.
