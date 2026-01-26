# Reference Papers (LaTeX Sources)

This directory contains LaTeX source files for key papers referenced in the thesis.
**Read the .tex files directly** - they are plain text and much more reliable than PDF parsing.

For the full workflow on adding new papers, see `.claude/skills/paper-reading/SKILL.md`.

## Available Papers

| Folder | arXiv | Citation | Key Content |
|--------|-------|----------|-------------|
| `HK2017-EHZ-polytopes/` | 1712.03494 | HK2017 | HK combinatorial capacity formula (Theorem 1) |
| `HK2024-counterexample/` | 2405.16513 | HK2024 | Pentagon x Pentagon counterexample |
| `CH2021-systolic/` | 2008.10111 | CH2021 | Chaidez-Hutchings computational methods |

## Quick Reference

```bash
# List papers
ls -la docs/papers/

# List files in a paper
ls -la docs/papers/CH2021-systolic/

# Find theorems/definitions across all papers
grep -rn "begin{theorem}\|begin{definition}" docs/papers/

# Find where a label is defined
grep -rn "\\label{" docs/papers/CH2021-systolic/

# Search all papers for a term
grep -rl "rotation" docs/papers/
```

## Key Sections

- **HK2017 Theorem 1**: The main EHZ capacity formula for polytopes
- **HK2017 Remark 4**: Alternative MIN formulation
- **CH2021 s1**: Rotation bounds and algorithm guidance
- **CH2021 s3**: Reeb dynamics on polytopes (the action derivation)

## Labels vs Numbers

TeX uses labels (`\label{thm:main}`), PDFs show numbers ("Theorem 3.2"). To find a label's definition:
```bash
grep -B2 -A10 "\\label{thm:main}" docs/papers/FOLDER/*.tex
```
See the paper-reading skill for detailed guidance on navigating this.
