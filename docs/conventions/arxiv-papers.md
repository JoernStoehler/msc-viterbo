# arXiv Paper Management

Downloading and organizing research papers in `docs/papers/`.

## Check Existing Papers First

```bash
ls -la docs/papers/
```

If folder exists, read `.tex` files directly. No download needed.

## Download Workflow

When paper is NOT in `docs/papers/` yet:

```bash
cd /workspaces/worktrees/<task>/
bash scripts/download-arxiv.sh <arxiv-id> <folder-name>

# Example:
bash scripts/download-arxiv.sh 2203.02043 Rudolf2022-worm-problem
```

**Folder naming:** `Initials + Year + description` (e.g., `HK2024-counterexample`)

Script auto-detects format (tar.gz or gzip'd single file) and extracts.

## After Download: Required Steps

1. **Update `docs/papers/README.md`** - add row to table with paper details

2. **Add BibTeX to `packages/latex_viterbo/references.bib`**:
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

## Navigating Downloaded Papers

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

## Why .tex Instead of PDF?

- Agents can read PDFs but transcription errors are common, especially in formulas
- PDFs consume more context window than `.tex` source
- Direct access to mathematical content without OCR issues
