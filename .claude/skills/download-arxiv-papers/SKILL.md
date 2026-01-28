---
name: download-arxiv-papers
description: Downloading arXiv papers for thesis research. Use when you need to find and read a new paper that is not already in /docs/papers/.
---

# arXiv Paper Management

## When to Use

- You found an arXiv paper via web search and need to read its actual content
- You need to verify formulas, definitions, or proofs from a paper
- A paper is repeatedly needed across sessions and should be cached locally

**Do NOT use** for papers you only need to cite without reading deeply. Just add a BibTeX entry to `packages/latex_viterbo/references.bib`.

## Location

Papers live in `docs/papers/`. Check existing folders first:
```bash
ls -la docs/papers/
```

## Download Workflow

**Use the download script** (requires TeX sources on arXiv):

```bash
# Clone download script from OLD_SKILLS_ARCHIVE.md if needed
# Then run:
bash .claude/skills/download-arxiv-papers/download-arxiv.sh <arxiv-id> <folder-name>

# Example:
bash .claude/skills/download-arxiv-papers/download-arxiv.sh 2203.02043 Rudolf2022-worm-problem
```

**Folder naming convention:**
- Single author: `Surname + Year + description` (e.g., `Rudolf2022-worm-problem`)
- Multiple authors: `Initials + Year + description` (e.g., `HK2024-counterexample`)

The script handles format detection (tar.gz vs gzip'd single file) automatically.

### After Downloading Checklist

1. **Update `docs/papers/README.md`** - add row to the table
2. **Add BibTeX to `packages/latex_viterbo/references.bib`** - websearch `arXiv <id>` for title/authors:
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
3. **Verify extraction** - `ls -la docs/papers/<folder>/` to see files

## Reading Papers

**Read the .tex files directly.** They are plain text and more reliable than PDF parsing.

**Watch for custom macros:** Some papers define shortcuts like `\bthm` instead of `\begin{theorem}`. If standard searches return nothing, check the preamble for `\def\bthm` or similar. Search for both patterns:

```bash
# Standard LaTeX theorem environments
grep -n "begin{theorem}\\|begin{definition}\\|begin{lemma}" docs/papers/FOLDER/*.tex

# Custom macros (common in some papers)
grep -n "\\\\bthm\\|\\\\blem\\|\\\\bprop\\|\\\\bdefi" docs/papers/FOLDER/*.tex

# Find all labels
grep -n "\\\\label{" docs/papers/FOLDER/*.tex
```

## Labels vs Numbers (TeX vs PDF)

TeX files use **labels** (e.g., `\label{thm:main}`), while PDFs show **numbers** (e.g., "Theorem 3.2").

**How to navigate**:

1. **Find where a label is defined** - the theorem text is right there:
   ```bash
   grep -B2 -A10 "\\\\label{thm:main}" docs/papers/FOLDER/*.tex
   ```

2. **Find all label definitions** to build a mental map:
   ```bash
   grep -n "\\\\label{" docs/papers/FOLDER/*.tex | head -30
   ```

3. **Labels are descriptive**: `thm:capacity`, `lem:rotation-bound` tell you more than numbers

4. **When humans reference by number**: Ask for label/section name, or look for context clues

**Do not rely on PDF for math content** - PDF parsing mangles formulas. Use PDF only to verify theorem numbering if absolutely necessary.

## Folder Naming Rationale

The scheme `CITATIONKEY-description/` with original filenames inside enables:
- **Discoverability**: Find papers by author, year, or topic via folder names
- **Citation linking**: Folder prefix matches `references.bib` entries
- **Intact references**: Internal `\input{section1}` still works
- **Easy browsing**: `ls -la` shows all paper files

## Why TeX over PDF

- TeX files are plain text, easy to grep and read
- PDF parsing in agents is unreliable for math notation
- Formulas appear exactly as the author wrote them
- Labels are searchable; following `\ref{}` is straightforward
- Smaller file size, faster to process
