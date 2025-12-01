# Writing the Thesis

- Goal: Write a professional-level master's thesis in mathematics.
- The thesis covers the entire project from the perspective of a mathematician, not from the perspective of a programmer or data scientist.
- Target audience are interested mathematicians with a background in symplectic geometry, but not necessarily any background in polytopes or Viterbo's conjecture, and no background in modern software engineering.
- The thesis must be self-contained. References to other parts of the repo are treated as further non-essential readings.
- Near the end of the project (several months away), we will refactor to LaTeX for final typesetting and submission, but we will keep the content nearly identical.

## Writing Style
The style we aim for is
- Literally correct and unambiguous. We are mathematically precise in what we do, to transfer deep understanding to the reader.
- Explicit, low cognitive overhead, complete, but skimmable. A reader who reads top to bottom should understand everything, using the usual ability to fill small gaps in natural language mathematical writing that is expected of professional mathematicians. We are actually leaning towards being very explicit and detailed, but structure our writing so that a reader can skip over details if they are faster at inferring them than reading them. In particular we clearly put proofs of statements into proof environments, so that a reader can skip them if they already believe the statement and are not interested in the proof strategy or proof details right now.
- Motivated. We explain the "why" behind definitions, theorems, proof layouts. Often there is a simple empirical reason that some definition covers more cases of interest than another, or that some definition is excluding edge cases that are different in a bothersome way but not relevant. Sometimes there are good reasons though for why some definition is natural, i.e. splits reality at the joints and is expected to match other natural definitions and theorems well.
- Structured. We help the reader navigate and skim the document by using clear headings, announce (spoiler) the takeaways early, and signpost the flow of the document well.
- Consistent notation. We pick notation that is similar to existing literature where possible, and consistent throughout the document. We often note when referenced documents deviate from our notation, so that readers who jump to those documents can translate easily in their heads.
- Clear distinction between mainline text and asides. We use admonitions and footnotes and references to appendices / optional sections.

## Toolchain
- Markdown in MkDocs + Material flavor. We heavily use Markdown-in-HTML as a style convention.
- We run `packages/thesis/scripts/lint.sh` to check for common issues. It runs `mkdocs build` under the hood.
- The project owner can preview the rendered thesis via `cd packages/thesis && mkdocs serve --livereload`. `mkdocs serve` does start, but its auto-reload loop is broken; the `--livereload` flag fixes reloads.
- The python experiments can generate static assets (plots as images, diagrams, tables) that we embed into the thesis. We store them under `packages/thesis/docs/assets/generated/` and commit them to the repo.

## Syntax Reminders
- Standard Markdown for most things.
- Use the **Blocks** `///` fences (pymdownx.blocks) instead of hand-written HTML:
  - Admonition: 
    ```
    /// admonition | Lemma (Upper Bound)
        type: lemma
        attrs: { name: "lem:upper-bound" }
    Statement of the lemma.
    ///
    ```
  - Proof (collapsible details):
    ```
    /// details | Proof
        type: proof
        open: true
    Proof details go here.
    ///
    ```
  - Figure/table captions (auto-numbered):
    ```
    ![Alt text](path/to/image.png)

    /// figure-caption
    Caption text.
    ///
    ```
    (use `table-caption` after a Markdown table for automatic table numbers.)
  - Tabs (avoid legacy `=== ""` syntax):
    ```
    /// tab | Python
        :::bash
        uv run python script.py
    ///

    /// tab | Rust
        :::bash
        cargo run --release
    ///
    ```
- LaTeX math: Arithmatex extension ( https://facelessuser.github.io/pymdown-extensions/extensions/arithmatex/ )
  - `\(...\)` for inline math, `\[...\]` for display math.
    ```math
    \begin{align}
      E &= mc^2 \\
      F &= ma
    \end{align}
    ```
  - We never use dollar signs because they cause bash escaping issues for agents who edit the files.
- Diagrams: mermaid
  ```mermaid
  graph TD;
      A-->B;
      A-->C;
      B-->D;
      C-->D;
  ```
- Tables: standard Markdown tables.
- Definition lists (enabled):
  ```
  Term
  : First definition line
  : Second definition line
  ```
- Lists: standard Markdown lists, nested as needed, ordered and unordered and task lists.
- The full extension list for MkDocs + Material is in `packages/thesis/mkdocs.yml`.
