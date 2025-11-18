# AGENTS – Docs Site Package

You are in `packages/docs-site/`, which hosts the public documentation and thesis site for the project. The site is built with Astro + MDX, so we can prerender everything into static HTML for GitHub Pages while still sprinkling in React/Vega islands for interactive plots.

## Responsibilities

- Render the thesis Markdown/MDX from `packages/thesis/src/` into an Astro site without mutating the source files.
- Co-host generated API docs from `packages/rust_viterbo`, `packages/python_viterbo`, and `packages/lean_viterbo` under `/api/*`.
- Provide shared layouts, typography, and UI components (callouts, theorem blocks, plot wrappers) that the thesis chapters can rely on.
- Offer hooks to embed interactive plot specs that were produced by the data pipelines while defaulting to the static fallbacks when JavaScript is disabled.

## Layout (initial)

- `src/pages/` – Glue pages such as the landing page, `/thesis` index, `/docs`, redirects. Astro/MDX files live here.
- `src/content/thesis/` – Symlink or copy of `packages/thesis/src/` prepared during build. Do not edit generated copies.
- `src/components/` – Theme primitives (layout, navigation) + interactive wrappers (`PlotIsland`, `FigureCompare`, etc.).
- `scripts/docs-publish.sh` – Entry point that builds per-package docs and runs `astro build`. Keeps the GitHub Pages pipeline self-contained in this package.
- `astro.config.mjs`, `package.json`, `tsconfig.json` – Standard Astro scaffolding (to be fleshed out in future issues).

## Build Workflow

1. Run the data+figure pipeline first (`uv run packages/python_viterbo/scripts/build_figures.py`). This emits JSON specs + static PNG/SVG siblings for every figure ID. Both files are committed.
2. From `packages/thesis/`, ensure MDX chapters reference figures by ID via the shared component API (see Thesis package docs).
3. Back in `packages/docs-site/`, execute `npm install` once, then `./scripts/docs-publish.sh` (see below). This script will:
   - collect thesis MDX files into `src/content/thesis/` (e.g. via `rsync`),
   - collect API docs into `public/api/*`,
   - run `npm run build` (Astro) and place the result into `dist/` ready for GitHub Pages.

## Scripts

`scripts/docs-publish.sh` is designed to be called from repo root CI or manually. It should be the only place that orchestrates documentation builds. Keep it POSIX-compatible and annotated, since other agents will extend it with concrete commands (`cargo doc`, `pdoc`, `lake`, `npm run build`, etc.).

## Conventions

- Treat this package as a read-only mirror of the thesis content; propose edits to the canonical Markdown inside `packages/thesis/`.
- Prefer widely-used Astro/React/Vega libraries. Avoid bespoke bundlers or CSS processors.
- Every interactive component must expose a `staticFallback` prop or similar so the print/PDF pipeline can degrade gracefully.
- Document any new commands in this file whenever you touch the docs-site tooling.
