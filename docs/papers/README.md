# Reference Papers (LaTeX Sources)

This directory contains LaTeX source files for key papers referenced in the thesis.
**Read the `.tex` files directly** - they are plain text and much more reliable than
attempting to parse PDFs.

## Available Papers

| File | arXiv | Citation | Key Content |
|------|-------|----------|-------------|
| `HK2017-EHZ-polytopes.tex` | 1712.03494 | HK2017 | HK combinatorial capacity formula (Theorem 1, lines 68-78) |
| `HK2024-counterexample.tex` | 2405.16513 | HK2024 | Pentagon×Pentagon counterexample |
| `systolic_paper.tex` + `s*.tex` | 2008.10111 | CH2021 | Chaidez-Hutchings computational methods |

## Usage for Agents

When implementing/debugging capacity algorithms, **read the actual formulas**:

```bash
# HK2017 formula - the core theorem
grep -A 20 "formula_theorem" docs/papers/HK2017-EHZ-polytopes.tex

# Find specific definitions
grep -n "ehzcap\|symplectic\|action" docs/papers/HK2017-EHZ-polytopes.tex
```

Key sections to check:
- **HK2017 Theorem 1 (lines ~68-78)**: The main capacity formula
- **HK2017 Remark 4 (lines ~95-110)**: Alternative MIN formulation
- **CH2021 s1_introduction**: Rotation bounds and algorithm guidance

## Adding New Papers

1. Download from arXiv: `wget https://arxiv.org/e-print/XXXX.XXXXX`
2. Extract: `tar -xzf XXXX.XXXXX`
3. Copy `.tex` files here with descriptive prefix
4. Update this README
