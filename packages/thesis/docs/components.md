# Components and Blocks (Thesis Markdown)

We now use plain Markdown + MkDocs. Avoid custom components; rely on familiar patterns that agents already know.

Math
- Inline math: `$...$`; display math: `$$...$$` (KaTeX via arithmatex).
- Keep TeX literal; avoid Unicode math symbols.

Structural blocks
- Theorem/Proposition/Lemma/Definition: use admonitions. Example:

  ```markdown
  !!! info "Theorem (Haim–Kislev 2024)"
      Statement text with math $\omega_0$.
  
  !!! note "Proof"
      Sketch of proof.
  ```

- Remark/Warning: `!!! tip` or `!!! warning`.
- Proof paragraphs can be inside a `!!! note` block or a plain paragraph prefixed with "Proof.".

Figures and plots
- Assets live under `src/assets/figures/<chapter>/` with paired static and interactive files, e.g. `fig-foo.png` and `fig-foo.json` (Plotly or Vega spec).
- Embed static image:

  ```markdown
  ![Caption for foo](assets/figures/ch1/fig-foo.png)
  ```

- Optional interactive Plotly hydration (served on GH Pages):

  ```markdown
  <div data-plot-json="assets/figures/ch1/fig-foo.json"></div>
  ```

  `assets/js/plotly-hydrate.js` loads the JSON and renders via the Plotly CDN. Keep JSON deterministic.

Cross-references
- Use standard Markdown links; MkDocs will resolve relative paths within `src/`.
- For equations, use labelled text (e.g., "(HK24, Thm. 1.1)") rather than custom numbering macros.

Do/Don’t
- Do keep everything Pandoc-friendly (plain Markdown + KaTeX + admonitions).
- Don’t add React/JSX/MDX syntax.
- Don’t invent new block types without updating this file and the build scripts.
