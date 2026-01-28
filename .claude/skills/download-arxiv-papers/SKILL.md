---
name: download-arxiv-papers
description: Downloading arXiv papers for thesis research. Use when you need to find and read a new paper that is not already in /docs/papers/.
---

# arXiv Paper Management

## Check Existing Papers First

```bash
ls -la docs/papers/
```

If the paper folder exists, just read the `.tex` files directly. No download needed.

## Download Workflow

When the paper is NOT in `docs/papers/` yet:

```bash
cd /workspaces/worktrees/<task>/
bash .claude/skills/download-arxiv-papers/download-arxiv.sh <arxiv-id> <folder-name>

# Example:
bash .claude/skills/download-arxiv-papers/download-arxiv.sh 2203.02043 Rudolf2022-worm-problem
```

**Folder naming convention:**
- `Initials + Year + description` (e.g., `HK2024-counterexample`)

The script automatically detects format (tar.gz or gzip'd single file) and extracts.

## After Downloading: Required Steps

1. **Update [docs/papers/README.md](docs/papers/README.md)** - add row to the table with paper details

2. **Add BibTeX to [packages/latex_viterbo/references.bib](packages/latex_viterbo/references.bib)** - websearch `arXiv <id>` for title/authors:
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

3. **Verify extraction worked**:
   ```bash
   ls -la docs/papers/<folder>/
   ```

## First-Time Navigation Tips

After downloading, you'll have raw `.tex` files. Quick tips for exploring:

**Find main content:**
```bash
# Look for main theorem/definition/lemma environments
grep -n "begin{theorem}\\|begin{definition}\\|begin{lemma}" docs/papers/FOLDER/*.tex

# Some papers use custom macros like \bthm - check preamble if standard search fails
grep -n "\\\\bthm\\|\\\\blem\\|\\\\bprop" docs/papers/FOLDER/*.tex
```

**Find specific results by label:**
```bash
# TeX uses labels (\label{thm:main}), not numbers ("Theorem 3.2")
grep -B2 -A10 "\\\\label{thm:main}" docs/papers/FOLDER/*.tex
```

**Why not PDF?**
- Agents can directly read PDFs, but transcription errors are common, including in formulas where they are impossible to catch.
- PDFs when read directly consume more context window budget than the source `.tex` files.
- Reading `.tex` source avoids OCR issues and allows direct access to mathematical content.
