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

1. Build docs inside each package (recommended commands):
   - Thesis: run your static exporter so output lands in `packages/thesis/build/site/` (e.g., `packages/thesis/scripts/build-site.sh` once available; for now pick any static MDX→HTML flow).
   - Rust: `cd packages/rust_viterbo && cargo doc --no-deps` (uses shared `worktrees/shared/target/doc/`).
   - Python: `cd packages/python_viterbo && uv run pdoc viterbo -o build/docs` (or your chosen Sphinx command to the same folder).
   - Lean: `cd packages/lean_viterbo && lake exe doc` (expected at `packages/lean_viterbo/build/doc`).
2. Run `packages/docs-site/scripts/docs-publish.sh` to copy those outputs into `public/thesis/` and `public/api/*`. The script warns if any docs are missing or older than sources.
3. Deploy GitHub Pages from `packages/docs-site/public/`.

## Scripts

`scripts/docs-publish.sh` is designed to be called from repo root CI or manually. It should be the only place that orchestrates documentation builds. Keep it POSIX-compatible and annotated, since other agents will extend it with concrete commands (`cargo doc`, `pdoc`, `lake`, `npm run build`, etc.).

## Conventions

- Do not edit or build thesis content here; only copy the already-built site.
- Keep `public/thesis/` and `public/api/*` gitignored; only `public/index.html` is tracked.
- If you extend the landing page or copy rules, document it here.
