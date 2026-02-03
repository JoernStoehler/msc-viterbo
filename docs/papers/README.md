# Reference Papers (LaTeX Sources)

This directory contains LaTeX source files for key papers referenced in the thesis.
**Read the .tex files directly** - they are plain text and much more reliable than PDF parsing.

## Available Papers

| Folder | arXiv | Citation | Key Content |
|--------|-------|----------|-------------|
| `HK2017-EHZ-polytopes/` | 1712.03494 | HK2017 | HK combinatorial capacity formula (Theorem 1); **this is HK's MSc thesis** |
| `HK2024-counterexample/` | 2405.16513 | HK2024 | Pentagon x Pentagon counterexample |
| `CH2021-systolic/` | 2008.10111 | CH2021 | Chaidez-Hutchings computational methods |
| `Rudolf2022-worm-problem/` | 2203.02043 | Rudolf2022 | Viterbo's conjecture as worm problem; Minkowski billiards |
| `Irie2019-loop-spaces/` | 1907.09749 | Irie2019 | SH capacity = EHZ capacity; HZ subadditivity |
| `AK2019-SH-clarke/` | 1907.07779 | AK2019 | Abbondandolo-Kang: SH via Clarke's dual action |
| `Irie2010-billiard-trajectory/` | 1010.3170 | Irie2010 | Short periodic billiard trajectory; at most n+1 bounces |

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

## Key Theorems (with line numbers)

Paper sources are frozen, so line numbers are stable references.

| Paper | Theorem | Line | Content |
|-------|---------|------|---------|
| HK2017 | Theorem 1 (`formula_theorem`) | 68 | EHZ capacity formula for polytopes |
| HK2017 | Theorem 2 | 130 | Subadditivity |
| HK2017 | Theorem 3 | 153 | Simple orbit suffices |
| Rudolf2022 | Theorem 1.1 (`Thm:relationship`) | 710 | c_EHZ = min billiard length for Lagrangian products |
| BezdekBezdek2009 | Theorem (`zero`) | 98 | Shortest billiard has period <= d+1 |
| BezdekBezdek2009 | Theorem (`first`) | 118 | Fat disk-polygon: shortest is 2-periodic |

## Key Sections

- **HK2017 Remark 4**: Alternative MIN formulation
- **CH2021 s1**: Rotation bounds and algorithm guidance
- **CH2021 s3**: Reeb dynamics on polytopes (the action derivation)

## Labels vs Numbers

TeX uses labels (`\label{thm:main}`), PDFs show numbers ("Theorem 3.2"). To find a label's definition:
```bash
grep -B2 -A10 "\\label{thm:main}" docs/papers/FOLDER/*.tex
```

---

## Download Workflow

When a paper is NOT in `docs/papers/` yet:

```bash
cd /workspaces/msc-viterbo
bash scripts/download-arxiv.sh <arxiv-id> <folder-name>

# Example:
bash scripts/download-arxiv.sh 2203.02043 Rudolf2022-worm-problem
```

**Folder naming:** `Initials + Year + description` (e.g., `HK2024-counterexample`)

Script auto-detects format (tar.gz or gzip'd single file) and extracts.

### After Download: Required Steps

1. **Update this README** - add row to Available Papers table

2. **Add BibTeX to `thesis/references.bib`**:
   ```bibtex
   @article{Rudolf2022,
     title        = {Viterbo's conjecture as a worm problem},
     author       = {Rudolf, Daniel},
     year         = {2022},
     journal      = {arXiv preprint},
     eprint       = {2203.02043},
     archivePrefix= {arXiv},
     primaryClass = {math.SG},
     note         = {Brief description of key results.}
   }
   ```

3. **Verify extraction**: `ls -la docs/papers/<folder>/`

### Navigating Downloaded Papers

Raw `.tex` files require different search patterns than PDFs.

**Find main content:**
```bash
# Standard theorem environments
grep -n "begin{theorem}\|begin{definition}\|begin{lemma}" docs/papers/FOLDER/*.tex

# Custom macros (check preamble if standard search fails)
grep -n "\\bthm\|\\blem\|\\bprop" docs/papers/FOLDER/*.tex
```

**Find by label:**
```bash
# TeX uses labels (\label{thm:main}), not numbers ("Theorem 3.2")
grep -B2 -A10 "\\label{thm:main}" docs/papers/FOLDER/*.tex
```

### Why .tex Instead of PDF?

- Agents can read PDFs but transcription errors are common, especially in formulas
- PDFs consume more context window than `.tex` source
- Direct access to mathematical content without OCR issues
