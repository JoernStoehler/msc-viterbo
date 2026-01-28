---
name: develop-latex
description: Editing the thesis or building PDF/HTML output. Use when writing thesis chapters, fixing LaTeX issues, or generating thesis documents.
---

# LaTeX/Thesis Development

## Commands

```bash
cd packages/latex_viterbo

scripts/lint.sh           # chktex + draft compile + latexml sanity
scripts/build.sh          # Full build (PDF + HTML)
scripts/build.sh --pdf-only
scripts/build.sh --html-only
scripts/serve.sh          # Watch mode
```

**Draft speedup:** Use `includeonly.tex` (copy from `includeonly.tex.example`)

## LaTeX Style

- **Inline math**: `\(...\)` not `$...$`
- **Display math**: `\[...\]` not `$$...$$`
- **Proofs**: Use `proof` environment
- **Label consistently**: Theorems, lemmas, equations
- **arXiv-friendly packages only**

## Thesis Writing Style

**Audience**: Symplectic geometers, self-contained exposition

**Principles**:
- **Separate mainline from asides**: Keep main argument clear
- **Introduce notation once**: Note deviations from literature
- **Explicit but skimmable**: Spoilers up front, headings guide reader
- **Mark WIP**: Use `\edit{}` or `%`

## Assets

- Python generates figures → `assets/<experiment>/`
- LaTeXML extras → `assets/{html/,latexml/}`
- Hand-crafted → `assets/manual/`
