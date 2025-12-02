# Writing the Thesis (LaTeX)

- Goal: Write a professional-level master's thesis in mathematics.
- Target audience: interested mathematicians with a background in symplectic geometry, but not necessarily any background in polytopes or Viterbo's conjecture, and no background in modern software engineering.
- The thesis must be self-contained. References to other parts of the repo are treated as non-essential further readings.
- Sources/output: LaTeX lives in `packages/latex_viterbo/`. PDF is primary; HTML is generated via `latexmlc`.

## Writing Style
The style we aim for is
- Literally correct and unambiguous. We are mathematically precise in what we do, to transfer deep understanding to the reader.
- Explicit, low cognitive overhead, complete, skimmable. A reader who reads top to bottom should understand everything, using the usual ability to fill small gaps in natural language mathematical writing that is expected of professional mathematicians. We are actually leaning towards being very explicit and detailed, but structure our writing so that a reader can skip over details if they are faster at inferring them than reading them. In particular we clearly put proofs of statements into proof environments, so that a reader can skip them if they already believe the statement and are not interested in the proof strategy or proof details right now.
- Motivated. We explain the "why" and "generating ideas" behind definitions, theorems, proofs. Often there is a simple empirical reason that some definition covers more cases of interest than another, or that some definition is excluding edge cases that are different in a bothersome way but not relevant. Sometimes there are good reasons though for why some definition is natural, i.e. splits reality at the joints and is expected to match other natural definitions and theorems well.
- Structured. We help the reader navigate and skim the document by using clear headings, announce (spoiler) the takeaways early, and signpost the flow of the document well.
- Consistent notation. We pick notation that is similar to existing literature where possible, and consistent throughout the document. We often note when referenced documents deviate from our notation, so that readers who jump to those documents can translate easily in their heads.
- Clear distinction between mainline text and asides. We use admonitions and footnotes and references to appendices / optional sections.

## Toolchain
- TeX Live (Ubuntu 24.04 packages ~TL2023), with latexml to create HTML output.
- Lint: `packages/latex_viterbo/scripts/lint.sh` (chktex + draft compile + latexml sanity).
- Build: `packages/latex_viterbo/scripts/build.sh [--production] [--pdf-only] [--html-only]` (draft to `build/`, production to `dist/`).
- Local serve: `packages/latex_viterbo/scripts/serve.sh [--production] [--watch] [--port 8000]` (serves draft/production HTML+PDF).
- CI: `.github/workflows/gh-pages.yml` builds and publishes artifacts on push to `main`.

## LaTeX Conventions and Syntax Reminders
- Follow best practices from ArXiv and standard LaTeX style guides.
- Math: `\(...\)` for inline, `\[...\]` for display; Avoid dollar signs since they cause shell escaping trouble for agents who edit files.
- Proofs: wrap proofs in the `proof` environment.
- Figures/tables: python pipelines store generated assets in `packages/latex_viterbo/assets/`.
- Chapters: Create a `includeonly.tex` (git-ignored) to control which chapters are included during draft builds.
- Bibliography: use `references.bib`.
- Packages/macros/styles: stick to well-known best-practice code snippets and packages; KISS, YAGNI.

