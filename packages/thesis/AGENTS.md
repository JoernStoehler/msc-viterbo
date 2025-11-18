# AGENTS – Thesis Package

You are in `packages/thesis/`, which contains the sources and build pipeline for the written MSc thesis **"Probing Viterbo's Conjecture"**.

## Strategy

- During development, the canonical sources are Markdown/MDX files (for consistency with the rest of the repo and for easy ingestion by the docs site).
- Roughly a week before submission, we convert the thesis to LaTeX and finalize the print-ready version there. The MDX stays authoritative; the LaTeX export is regenerated whenever tweaks are needed.

## Layout (initial)

- `src/` – Markdown sources, e.g. chapters and sections.
- `build/` – generated artifacts (PDF, LaTeX), gitignored.

## Architecture context

- Every claim in the thesis should reference reproducible artifacts: algorithms from `packages/rust_viterbo`, experiments from `packages/python_viterbo`, proofs from `packages/lean_viterbo`.
- Keep citations to code/lemmas stable by referencing commit hashes or tagged releases when available.
- When the thesis build process changes (e.g. switching from Markdown → LaTeX), document the workflow here so automation agents can follow it without re-reading history.

## Source format & components

- Author every chapter as `.mdx` inside `src/`. Each file starts with YAML front matter:

  ```yaml
  ---
  title: Probing Viterbo's Conjecture
  slug: overview
  summary: >
    Short abstract for web previews.
  figures:
    - id: fig-ball-sys
      caption: Symplectic systole for the 4-ball.
      assets:
        interactive: figures/fig-ball-sys.json
        static: figures/fig-ball-sys.png
  ---
  ```

- Keep prose in plain Markdown. Use a tiny component palette in `src/components/` (e.g. `Callout`, `Definition`, `FigureBlock`) so both the docs site and the Pandoc exporter can map them to layouts/LaTeX environments.
- Every MDX component must implement:
  - `renderStatic(props)` to produce pure Markdown/HTML that Pandoc can consume.
  - `renderInteractive(props)` for docs-site/React islands. The exporter selects which rendering to use.
- Components should depend only on widely used packages (React, rehype, Remark). No local build steps.

## Figures and assets

- Numerical experiments live in `packages/python_viterbo/`. Extend its pipelines to emit both interactive specs (`.json`, `.plotly`, `.vg.json`, etc.) and static siblings (`.png`/`.svg`) for each figure ID. Store them under `src/assets/figures/<chapter>/<figure-id>.*`.
- Treat figure IDs as the API surface: MDX imports the `FigureBlock` component and references assets by ID; the docs site loads the JSON for interactivity, whereas the Pandoc export swaps the reference with the static PNG automatically.
- Always commit the static assets. Interactive specs can be re-generated but should remain deterministic (pin seeds and commits of upstream code).
- Animated figures (gif/webm) must include a poster PNG named `<id>.poster.png` for the print pipeline.

## Interaction with `packages/docs-site/`

- `packages/docs-site/` rsyncs `packages/thesis/src/` into `packages/docs-site/src/content/thesis/` before running Astro. Do not place build artifacts in `src/`; keep generated files inside `build/`.
- Shared component contracts live here; when adding a new MDX component, document its props in this file and update the docs-site component library to match.
- Navigation metadata (`slug`, `summary`, `order`) lives solely in the MDX front matter so that both the docs site and the PDF exporter read the same data.

## Export workflows

- **Docs / GitHub Pages**: run `packages/docs-site/scripts/docs-publish.sh`. That script (to be extended) will gather API docs, copy MDX sources, and execute `pnpm astro build`.
- **Print / PDF**: add `build/pandoc/` with templates + filters. The export script should:
  1. Re-run the figure pipeline in static mode.
  2. Strip interactive components via their `renderStatic` helpers.
  3. Use Pandoc (`gfm+yaml_metadata_block` → LaTeX) followed by `tectonic` or `latexmk`.
  Keep the full workflow scripted so re-running it shortly before submission is <1 day of work.

## Tooling and commands

- Until the concrete Pandoc/LaTeX tooling lands, focus on writing MDX that adheres to the conventions above and includes references to reproducible artifacts (Rust, Python, Lean).
- Whenever you touch the export or docs-site integration, update this file so future agents inherit the workflow verbatim.
