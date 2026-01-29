# LaTeX Development

Commands and conventions for thesis development in `packages/latex_viterbo/`.

## Commands

```bash
cd /workspaces/worktrees/<task>/packages/latex_viterbo

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
- **Cross-references**: Use `\ref{}` not hardcoded numbers; use `\eqref{}` for equations
- **Custom macros**: Define in preamble, not inline (e.g., `\newcommand{\Sp}{\operatorname{Sp}}`)
- **arXiv-friendly packages only**

## Assets

| Type | Location |
|------|----------|
| Python-generated figures | `assets/<experiment>/` |
| LaTeXML extras | `assets/{html/,latexml/}` |
| Hand-crafted | `assets/manual/` |

## Work-in-Progress Markers

- Use `\edit{...}` or `% TODO: ...` for incomplete sections
- Remove all WIP markers before final submission
