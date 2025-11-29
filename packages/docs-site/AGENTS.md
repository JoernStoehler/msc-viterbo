# AGENTS – Docs Site Package

You are in `packages/docs-site/`, a thin static host for all docs outputs. Packages build their own HTML; this package just copies them into `public/` for GitHub Pages.

## Responsibilities

- Host the thesis static export under `/thesis/` (built inside `packages/thesis/`).
- Host generated API docs from `packages/rust_viterbo`, `packages/python_viterbo`, and `packages/lean_viterbo` under `/api/*`.
- Provide a tiny landing page (`public/index.html`) linking to each doc set.

## Layout (initial)

- `public/` – Served as-is by GitHub Pages. Contains `index.html` (landing) plus copied outputs under `public/thesis/` and `public/api/*`.
- `scripts/docs-publish.sh` – Single entry point: builds all package docs, stages them into `public/`, and publishes to `gh-pages` (can skip via env flags).
- (deprecated) `scripts/stage-hub.sh` / `scripts/publish-ghpages.sh` – removed; staging/publish now lives inside `docs-publish.sh`.

## Build Workflow

1. One-shot pipeline: `packages/docs-site/scripts/docs-publish.sh` builds all package docs, stages them into `public/`, and publishes to `gh-pages` via a temporary worktree. It fails fast on errors. Optional flags: `SKIP_THESIS=1`, `SKIP_RUST=1`, `SKIP_PYTHON=1`, `SKIP_LEAN=1`, `SKIP_PUBLISH=1`; you can also set `LEAN_DOCS=0` to skip Lean docs. Lean docs use a shared cache: warm builds are ~30s; a cold build (cache wiped) can take ~20–25m.
2. Internals of the one-shot pipeline (for troubleshooting):
   - Thesis: `packages/thesis/scripts/build-site.sh` (MkDocs) → `packages/thesis/build/site/`.
   - Rust: `packages/rust_viterbo/scripts/build-docs.sh` (cargo doc) → `${CARGO_TARGET_DIR:-.}/doc` (defaults to the shared target dir from `.cargo/config.toml`).
   - Python: `packages/python_viterbo/scripts/build-docs.sh` (pdoc) → `packages/python_viterbo/build/docs/`.
   - Lean: `packages/lean_viterbo/scripts/build-docs.sh` (lake exe doc) → `packages/lean_viterbo/build/doc/`.
   - Stage: built into `docs-publish.sh` (copies into `public/thesis/` and `public/api/*`, warns on stale/missing outputs).
   - Publish: built into `docs-publish.sh` (gh-pages worktree, commit, push).

## Scripts

`scripts/docs-publish.sh` is designed to be called from repo root CI or manually. It orchestrates all builds and publish. Keep it POSIX-compatible and annotated if you extend it.

## Conventions

- Do not edit or build thesis content here; only copy the already-built site.
- Keep `public/thesis/` and `public/api/*` gitignored; only `public/index.html` is tracked.
- If you extend the landing page or copy rules, document it here.
