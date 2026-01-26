# Reference Papers (LaTeX Sources)

This directory contains LaTeX source files for key papers referenced in the thesis.
**Read the `.tex` files directly** - they are plain text and much more reliable than
attempting to parse PDFs.

For the full workflow on adding new papers, see `.claude/skills/paper-reading/SKILL.md`.

## Available Papers

| File | arXiv | Citation | Key Content |
|------|-------|----------|-------------|
| `HK2017-EHZ-polytopes.tex` | 1712.03494 | HK2017 | HK combinatorial capacity formula (Theorem 1) |
| `HK2024-counterexample.tex` | 2405.16513 | HK2024 | Pentagon x Pentagon counterexample |
| `systolic_paper.tex` + `s*.tex` + `a*.tex` | 2008.10111 | CH2021 | Chaidez-Hutchings computational methods |

## Naming Convention

- Pattern: `CITATIONKEY-short-description.tex`
- Citation key: Author initials + year (e.g., `HK2017`, `CH2021`)
- Multi-file papers: Use consistent prefix (e.g., `CH2021-systolic-s1.tex`, `CH2021-systolic-s2.tex`)

## Quick Reference

```bash
# Find theorems and definitions
grep -n "begin{theorem}\|begin{definition}" docs/papers/*.tex

# HK2017 main formula
grep -A 10 "ehzcap" docs/papers/HK2017-EHZ-polytopes.tex

# Search all papers for a term
grep -l "rotation" docs/papers/*.tex
```

## Key Sections

- **HK2017 Theorem 1**: The main EHZ capacity formula for polytopes
- **HK2017 Remark 4**: Alternative MIN formulation
- **CH2021 s1**: Rotation bounds and algorithm guidance
- **CH2021 s3**: Reeb dynamics on polytopes (the action derivation)
