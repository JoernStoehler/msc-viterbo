# AGENTS – Docs Site Package

You are in `packages/docs-site/`, which is now a thin static host for all docs outputs. Packages build their own HTML; this package just copies them into `public/` for GitHub Pages.

## Responsibilities

- Host the thesis static export under `/thesis/` (built inside `packages/thesis/`).
- Host generated API docs from `packages/rust_viterbo`, `packages/python_viterbo`, and `packages/lean_viterbo` under `/api/*`.
- Provide a tiny landing page (`public/index.html`) linking to each doc set.

## Layout (initial)

- `public/` – Served as-is by GitHub Pages. Contains `index.html` (landing) plus copied outputs under `public/thesis/` and `public/api/*`.
- `scripts/docs-publish.sh` – Single entry point: wipes `public/thesis` and `public/api`, copies built artifacts from each package, leaves the landing page untouched. Does not run builds.
- `package.json` – Only a placeholder; no build tooling lives here now.

## Build Workflow

1. Build docs inside each package:
   - Thesis static site → `packages/thesis/build/site/` (choose your builder: Astro static/Pandoc/etc.).
   - Rust API → `worktrees/shared/target/doc/` via `cargo doc`.
   - Python API → `packages/python_viterbo/build/docs/` via `pdoc` or Sphinx.
   - Lean docs → `packages/lean_viterbo/build/doc/` via `lake exe doc`.
2. Run `packages/docs-site/scripts/docs-publish.sh` to copy those outputs into `public/thesis/` and `public/api/*`.
3. Deploy GitHub Pages from `packages/docs-site/public/`.

## Scripts

`scripts/docs-publish.sh` is designed to be called from repo root CI or manually. It should be the only place that orchestrates documentation builds. Keep it POSIX-compatible and annotated, since other agents will extend it with concrete commands (`cargo doc`, `pdoc`, `lake`, `npm run build`, etc.).

## Conventions

- Do not edit or build thesis content here; only copy the already-built site.
- Keep `public/thesis/` and `public/api/*` gitignored; only `public/index.html` is tracked.
- If you extend the landing page or copy rules, document it here.
