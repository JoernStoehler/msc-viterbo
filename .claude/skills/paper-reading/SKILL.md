---
name: paper-reading
description: Add arXiv papers to the repo for agent access. Use when you need to read a paper's formulas/proofs, or when web search gives you an arXiv ID you want to examine closely.
---

# Paper Reading (arXiv sources)

## When to use this skill

- You found an arXiv paper via web search and need to read its actual content
- You need to verify formulas, definitions, or proofs from a paper
- A paper is repeatedly needed across sessions and should be cached locally

**Do NOT use** for papers you only need to cite without reading deeply.

**Delegation tip**: If you're doing implementation work and need to understand a paper, consider spawning a subagent to read and summarize the relevant sections. This keeps your main context clean for code.

## Location

Papers live in `docs/papers/`. Check existing folders first:
```bash
ls -la docs/papers/
```

## [proposed] Download workflow

1. **Get arXiv ID** from URL (e.g., `https://arxiv.org/abs/2405.16513` -> ID is `2405.16513`)

2. **Create folder** with naming convention:
   - Pattern: `docs/papers/CITATIONKEY-short-description/`
   - Citation key: Author initials + year (matches BibTeX)
   - Examples: `HK2017-EHZ-polytopes/`, `CH2021-systolic/`

3. **Download and extract source** (TeX, not PDF):
   ```bash
   mkdir -p docs/papers/HK2024-counterexample
   cd docs/papers/HK2024-counterexample
   wget https://arxiv.org/e-print/2405.16513 -O source.tar.gz
   tar -xzf source.tar.gz
   rm source.tar.gz
   ls -la  # see what files extracted
   ```

   **Keep source files as-is** - don't rename them. They may have internal `\input{}` references that would break.

4. **Update docs/papers/README.md** table with:
   - Folder name
   - arXiv ID
   - Citation key
   - Key content description

5. **Add BibTeX entry** to `packages/latex_viterbo/references.bib`:
   ```bibtex
   @article{HK2024,
     title        = {A Counterexample to Viterbo's Conjecture},
     author       = {Haim-Kislev, Pazit and Ostrover, Yaron},
     year         = {2024},
     journal      = {arXiv preprint},
     eprint       = {2405.16513},
     archivePrefix= {arXiv},
     primaryClass = {math.SG},
     note         = {Brief description of key results.}
   }
   ```

## [proposed] Reading papers

**Read the .tex files directly.** They are plain text and more reliable than PDF parsing.

```bash
# List files in a paper folder
ls -la docs/papers/CH2021-systolic/

# Find theorems, definitions, lemmas
grep -n "begin{theorem}\|begin{definition}\|begin{lemma}" docs/papers/HK2017-EHZ-polytopes/*.tex

# Find where a label is defined
grep -n "\\\\label{" docs/papers/CH2021-systolic/*.tex
```

## [proposed] Labels vs Numbers (TeX vs PDF)

TeX files use **labels** (e.g., `\label{thm:main}`), while PDFs show **numbers** (e.g., "Theorem 3.2"). This matters when:
- A human asks about "Theorem 3.2" but you're reading TeX
- You find `\ref{thm:capacity}` and need to locate its definition

**How to navigate**:

1. **Find where a label is defined** - the theorem text is right there:
   ```bash
   grep -B2 -A10 "\\\\label{thm:main}" docs/papers/FOLDER/*.tex
   ```

2. **Find all label definitions** to build a mental map:
   ```bash
   grep -n "\\\\label{" docs/papers/FOLDER/*.tex | head -30
   ```

3. **Labels often hint at content**: `thm:capacity`, `lem:rotation-bound`, `def:ehz` are more descriptive than numbers.

4. **When humans reference by number**: Ask them for the label or section name, or look for context clues ("the main theorem in section 3" → grep for `\section{` to find section 3, then look for theorems there).

**Do not rely on PDF for math content** - PDF parsing mangles formulas (missing signs, broken fractions, extra symbols). Use PDF only to verify theorem numbering if absolutely necessary.

## [proposed] Folder naming rationale

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
