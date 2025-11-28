# AGENTS – Docs Site Package

You are in `packages/docs-site/`, which hosts the public documentation and thesis site for the project. The site is built with Astro + MDX to prerender static HTML for GitHub Pages while still allowing React/Vega islands for interactive plots.

## Responsibilities

- Render the thesis Markdown/MDX from `packages/thesis/src/` into an Astro site without mutating the source files (they are rsynced into `src/content/thesis/`).
- Co-host generated API docs from `packages/rust_viterbo`, `packages/python_viterbo`, and `packages/lean_viterbo` under `/api/*`.
- Provide shared layouts, typography, and UI components (callouts, theorem blocks, plot wrappers) that the thesis chapters can rely on.
- Offer hooks to embed interactive plot specs that were produced by the data pipelines while defaulting to the static fallbacks when JavaScript is disabled.

## Layout (initial)

- `src/pages/` – Glue pages such as the landing page, `/thesis` index, `/docs`, redirects. Astro/MDX files live here.
- `src/content/thesis/` – Rsync copy of `packages/thesis/src/` prepared during `scripts/docs-publish.sh`. Do not edit generated copies (gitignored).
- `src/components/` – Theme primitives (layout, navigation) + interactive wrappers (`PlotIsland`, `FigureCompare`, etc.).
- `scripts/docs-publish.sh` – Single entry point: stages thesis MDX, copies any prebuilt API docs, installs deps if needed, then runs `astro build`. Keeps GitHub Pages orchestration inside this package.
- `astro.config.mjs`, `package.json`, `tsconfig.json` – Standard Astro scaffolding (to be fleshed out in future issues).

## Build Workflow

1. Run per-package doc builds yourself (e.g., `cargo doc`, `uv run pdoc`, `lake exe doc`). Outputs should land under `packages/<pkg>/build/docs` (Python/Lean) or `worktrees/shared/target/doc` (Rust).
2. Keep thesis sources authoritative in `packages/thesis/src/`; add figure assets there. Do not edit `src/content/thesis/` directly.
3. From `packages/docs-site/`, execute `npm install` once, then `./scripts/docs-publish.sh`. The script will rsync thesis sources into `src/content/thesis/`, copy any built API docs into `public/api/*`, and run `npm run build` (Astro) to create `dist/` for GitHub Pages.

## Scripts

`scripts/docs-publish.sh` is designed to be called from repo root CI or manually. It should be the only place that orchestrates documentation builds. Keep it POSIX-compatible and annotated, since other agents will extend it with concrete commands (`cargo doc`, `pdoc`, `lake`, `npm run build`, etc.).

## Conventions

- Treat this package as a read-only mirror of the thesis content; propose edits to the canonical Markdown inside `packages/thesis/`.
- Prefer widely-used Astro/React/Vega libraries. Avoid bespoke bundlers or CSS processors.
- Every interactive component must expose a `staticFallback` prop or similar so the print/PDF pipeline can degrade gracefully.
- Document any new commands in this file whenever you touch the docs-site tooling.
