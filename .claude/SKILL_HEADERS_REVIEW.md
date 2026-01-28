# Skill Headers for Review

All skills with YAML frontmatter only. Review names and descriptions before bodies are written.

---

## develop-rust

```yaml
name: develop-rust
description: Writing or testing Rust code in packages/rust_viterbo. Use when implementing algorithms, writing tests, fixing bugs, or working with the Rust codebase.
```

**Purpose:** Core Rust development workflows

---

## develop-python

```yaml
name: develop-python
description: Writing or testing Python code in packages/python_viterbo. Use when creating experiments, writing analysis stages, or working with the Python codebase.
```

**Purpose:** Core Python development and experiment workflows

---

## develop-latex

```yaml
name: develop-latex
description: Editing the thesis or building PDF/HTML output. Use when writing thesis chapters, fixing LaTeX issues, or generating thesis documents.
```

**Purpose:** Thesis writing and document generation

---

## develop-python-rust-interop

```yaml
name: develop-python-rust-interop
description: Building or modifying Rust-Python FFI bindings using PyO3 and maturin. Use when exposing Rust algorithms to Python or fixing FFI issues.
```

**Purpose:** FFI work (infrequent but important)

---

## develop-codespace

```yaml
name: develop-codespace
description: Working with development environments, git worktrees for parallel agents, or modifying devcontainer configuration. Use when setting up worktrees, troubleshooting environment issues, or changing toolchain.
```

**Purpose:** Environment management and parallel agent workflows via worktrees

---

## plan-experiments

```yaml
name: plan-experiments
description: Planning or executing thesis research experiments. Use when designing experiments, writing SPEC.md files, organizing experiment stages, or tracking experiment progress.
```

**Purpose:** Experiment lifecycle management

---

## plan-tasks

```yaml
name: plan-tasks
description: Adding or reorganizing tasks in TODO.md. Use when Jörn requests task additions, when discovered work needs tracking, or when restructuring the task list. NOT for normal task completion (marking [x]).
```

**Purpose:** Task management (infrequent - Jörn manages backlog)

---

## review-math-docs-code-correspondence

```yaml
name: review-math-docs-code-correspondence
description: Verifying that code correctly implements mathematical specifications from the thesis. Use when checking formula correspondence, validating numerical algorithms, or ensuring code matches thesis definitions.
```

**Purpose:** Mathematical correctness verification

---

## review-thesis-writing-style

```yaml
name: review-thesis-writing-style
description: Reviewing thesis writing quality, clarity, and style. Use when checking exposition for symplectic geometer audience, improving readability, or ensuring LaTeX formatting conventions are followed.
```

**Purpose:** Thesis quality and style review

---

## download-arxiv-papers

```yaml
name: download-arxiv-papers
description: Downloading and reading arXiv papers for thesis research. Use when you need to read a paper's actual formulas and proofs (not just cite it), or when web search gives you an arXiv ID to examine closely.
```

**Purpose:** Paper management and TeX source reading

---

## Notes

**Kept as-is:**
- `skill-creator` - Already well-structured (official skill from Anthropic)

**Not included:**
- `official-claude-code-guides` - This appears to have been removed from the old skills archive. Should we keep it or is it redundant with the built-in claude-code-guide agent?

---

## Feedback Requested

1. **Names**: Are skill names clear and consistent?
2. **Descriptions**: Do the trigger descriptions capture when each skill should be used?
3. **Missing**: Any workflows missing from this list?
4. **Redundant**: Any skills that could be merged?
