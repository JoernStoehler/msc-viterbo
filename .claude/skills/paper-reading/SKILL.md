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

## Location

Papers live in `docs/papers/`. Read the existing papers there first to see what's already available.

## [proposed] Download workflow

1. **Get arXiv ID** from URL (e.g., `https://arxiv.org/abs/2405.16513` -> ID is `2405.16513`)

2. **Download source** (TeX, not PDF):
   ```bash
   cd /tmp
   wget https://arxiv.org/e-print/2405.16513 -O paper.tar.gz
   tar -xzf paper.tar.gz
   ls -la  # see what files extracted
   ```

3. **Copy to docs/papers/** with naming convention:
   - Pattern: `CITATIONKEY-short-description.tex`
   - Citation key: Author initials + year (matches BibTeX)
   - Examples: `HK2017-EHZ-polytopes.tex`, `CH2021-systolic-computation.tex`

   For multi-file papers (common for long papers):
   ```bash
   # Keep the main file and sections, prefix them consistently
   cp main.tex /home/user/msc-viterbo/docs/papers/CH2021-systolic-main.tex
   cp section1.tex /home/user/msc-viterbo/docs/papers/CH2021-systolic-s1.tex
   ```

4. **Update docs/papers/README.md** table with:
   - File name
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

Once downloaded, **read the .tex files directly**. They are plain text and more reliable than PDF parsing.

```bash
# Find specific content
grep -n "Theorem\|Definition\|Lemma" docs/papers/HK2017-EHZ-polytopes.tex

# Read around a specific line
Read tool with offset/limit for specific sections
```

## [proposed] Naming convention rationale

The naming scheme `CITATIONKEY-description.tex` enables:
- **Discoverability**: Agents can find papers by author, year, or topic via glob/grep
- **Citation linking**: Citation key matches `references.bib` entries
- **Multi-file coherence**: Related files share the prefix

## Why TeX over PDF

- TeX files are plain text, easy to grep and read
- PDF parsing in agents is unreliable for math notation
- Formulas appear exactly as the author wrote them
- Smaller file size, faster to process
