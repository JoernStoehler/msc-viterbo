# AGENTS – Thesis Package

You are in `packages/thesis/`, which contains the sources and build pipeline for the written MSc thesis **"Probing Viterbo's Conjecture"**.

## Strategy

- During development, the canonical sources are Markdown files (for consistency with the rest of the repo).
- Roughly a week before submission, we convert the thesis to LaTeX and finalize the print-ready version there.

## Layout (initial)

- `src/` – Markdown sources, e.g. chapters and sections.
- `build/` – generated artifacts (PDF, LaTeX), gitignored.

## Architecture context

- Every claim in the thesis should reference reproducible artifacts: algorithms from `packages/rust_viterbo`, experiments from `packages/python_viterbo`, proofs from `packages/lean_viterbo`.
- Keep citations to code/lemmas stable by referencing commit hashes or tagged releases when available.
- When the thesis build process changes (e.g. switching from Markdown → LaTeX), document the workflow here so automation agents can follow it without re-reading history.

## Tooling and commands

- The concrete build pipeline (e.g. pandoc-based) will be defined in future GitHub issues.
- For now, focus on content organization and keeping Markdown in sync with results, code, and proofs.
