# AGENTS – Docs Site Package

You are in `packages/docs-site/`, a thin static host for all docs outputs. Packages build their own HTML; this package just copies them into `public/` for GitHub Pages.

## Responsibilities

- Host the thesis static export under `/thesis/` (built inside `packages/thesis/`).
- Host generated API docs from `packages/rust_viterbo`, `packages/python_viterbo`, and `packages/lean_viterbo` under `/api/*`.
- Provide a tiny landing page (`public/index.html`) linking to each doc set.

## Layout (initial)

- `public/` – Served as-is by GitHub Pages. Contains `index.html` (landing) plus copied outputs under `public/thesis/` and `public/api/*`.
- `scripts/docs-publish.sh` – Single entry point: wipes `public/thesis` and `public/api`, copies built artifacts from each package, leaves the landing page untouched. Does not run builds.
- `package.json` – Placeholder with a `noop` script; no dependencies.

## Build Workflow

1. One-shot pipeline: `packages/docs-site/scripts/docs-publish.sh` builds all package docs, stages them into `public/`, and publishes to `gh-pages` via a temporary worktree. It fails fast on errors. Optional SKIP flags: `SKIP_THESIS=1`, `SKIP_RUST=1`, `SKIP_PYTHON=1`, `SKIP_LEAN=1`, `SKIP_PUBLISH=1`.
2. Internals of the one-shot pipeline (for troubleshooting):
   - Thesis: `packages/thesis/scripts/build-site.sh` → `packages/thesis/build/site/` (currently a TODO stub; implement static export there).
   - Rust: `packages/rust_viterbo/scripts/build-docs.sh` (cargo doc) → `worktrees/shared/target/doc/`.
   - Python: `packages/python_viterbo/scripts/build-docs.sh` (pdoc) → `packages/python_viterbo/build/docs/`.
   - Lean: `packages/lean_viterbo/scripts/build-docs.sh` (lake exe doc) → `packages/lean_viterbo/build/doc/`.
   - Stage: `scripts/stage-hub.sh` copies builds into `public/thesis/` and `public/api/*` and warns on stale/missing outputs.
   - Publish: `scripts/publish-ghpages.sh` copies `public/` into a `gh-pages` worktree, commits, and pushes.

## Scripts

`scripts/docs-publish.sh` is designed to be called from repo root CI or manually. It should be the only place that orchestrates documentation builds. Keep it POSIX-compatible and annotated, since other agents will extend it with concrete commands (`cargo doc`, `pdoc`, `lake`, `npm run build`, etc.).

## Conventions

- Do not edit or build thesis content here; only copy the already-built site.
- Keep `public/thesis/` and `public/api/*` gitignored; only `public/index.html` is tracked.
- If you extend the landing page or copy rules, document it here.
