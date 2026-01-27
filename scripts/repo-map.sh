#!/usr/bin/env bash
# Prints a compact repo map: pwd, git status, and file tree
# Run this when you need to understand the project structure

set -e

if [[ ${1:-} == "--help" || ${1:-} == "-h" ]]; then
  cat <<'EOF'
Usage: scripts/repo-map.sh

Prints pwd, git status (porcelain v2), and a compact repo tree.
Use this to get an overview of the project structure.

The tree auto-collapses large directories and hides build artifacts.
See inline CONFIG in this script to adjust skip/hide/collapse rules.
EOF
  exit 0
fi

if [[ $# -gt 0 ]]; then
  echo "Unknown flag: $1" >&2
  exit 1
fi

echo "[repo-map] pwd"
pwd

echo "[repo-map] git status --porcelain=v2 -b"
git status --porcelain=v2 -b

echo "[repo-map] file tree"
printf '%s\n' "$PWD"
python3 - <<'PY'
"""
repo-map.sh tree printer

Tiers (editable):
  - must_show: always expanded
  - skip_names/prefixes: shown once then collapsed (no children)
  - hide_names: omitted entirely

Auto-collapse if too many descendants (collapse_threshold) or depth_limit is
exceeded. Hard-truncate if the rendered tree would exceed budget_lines. Adjust
the CONFIG block when the repo structure changes.
"""
from pathlib import Path
from types import SimpleNamespace

# ---------- configuration (edit when the repo structure changes) ----------
CONFIG = SimpleNamespace(
    must_show={
        Path("packages"),
        Path("packages/latex_viterbo"),
        Path("packages/rust_viterbo"),
        Path("packages/python_viterbo"),
        Path("scripts"),
        Path(".devcontainer"),
        Path(".github"),
        Path(".claude"),
        Path("README.md"),
        Path("LICENSE"),
        Path("msc-viterbo.code-workspace"),
    },
    skip_names={
        ".git",
        ".venv",
        "build",
        "dist",
        "site-packages",
        "site",
        "target",
        ".latexmk",
    },
    skip_prefixes={"_minted"},  # match directory names starting with these prefixes
    hide_names={  # completely omitted (not even a collapsed marker)
        "__pycache__",
        ".pytest_cache",
        ".mypy_cache",
        ".ruff_cache",
        ".ipynb_checkpoints",
    },
    collapse_threshold=120,
    budget_lines=250,
    depth_limit=5,  # applied only outside must_show
)


# -------------------------- helper functions -----------------------------
root = Path(".").resolve()


def is_must_show(rel: Path) -> bool:
    return rel in CONFIG.must_show


def is_skip(rel: Path) -> bool:
    name = rel.name
    if name in CONFIG.skip_names:
        return True
    if any(name.startswith(pfx) for pfx in CONFIG.skip_prefixes):
        return True
    return False


def list_children(rel: Path):
    base = root / rel
    children = []
    for p in sorted(base.iterdir(), key=lambda x: (not x.is_dir(), x.name.lower())):
        name = p.name
        if name in CONFIG.hide_names:
            continue
        if p.is_symlink():
            continue  # avoid cycles
        child_rel = rel / name
        children.append((child_rel, p.is_dir()))
    return children


def descendant_count(rel: Path, threshold: int | None):
    """Count descendants, respecting hide/skip, early-out if threshold exceeded."""
    files = dirs = 0
    base = root / rel
    if not base.is_dir():
        return files, dirs
    for p in base.rglob("*"):
        if p.is_symlink():
            continue
        name = p.name
        rel_p = Path(p.relative_to(root))
        if name in CONFIG.hide_names or is_skip(rel_p):
            continue
        if p.is_dir():
            dirs += 1
        else:
            files += 1
        if threshold and files + dirs > threshold:
            break
    return files, dirs


def should_collapse(rel: Path, depth: int, threshold: int | None):
    abs_path = root / rel
    if not abs_path.is_dir():
        return False  # never collapse individual files
    if is_skip(rel):
        return True
    if is_must_show(rel):
        return False
    if depth > CONFIG.depth_limit:
        return True
    if threshold:
        files, dirs = descendant_count(rel, threshold)
        if files + dirs > threshold:
            return True
    return False


def render(threshold: int | None):
    lines = []

    def walk(rel: Path, prefix: str, last: bool, depth: int):
        abs_path = root / rel
        is_dir = abs_path.is_dir()
        label = rel.name + ("/" if is_dir else "")
        collapsed = should_collapse(rel, depth, threshold)

        empty = is_dir and not collapsed and not list_children(rel)
        connector = "└── " if last else "├── "
        if empty:
            suffix = " (empty)"
        elif collapsed:
            suffix = " (collapsed)"
        else:
            suffix = ""

        lines.append(f"{prefix}{connector}{label}{suffix}")

        if collapsed or empty or not is_dir:
            return

        new_prefix = prefix + ("    " if last else "│   ")
        kids = list_children(rel)
        for idx, (child_rel, is_dir_child) in enumerate(kids):
            walk(child_rel, new_prefix, idx == len(kids) - 1, depth + 1)

    lines.append(".")
    top_children = list_children(Path("."))
    for idx, (rel, is_dir) in enumerate(top_children):
        walk(rel, "", idx == len(top_children) - 1, 1)
    return lines


def render_with_budget():
    """
    Single-pass render with a simple guard for very large outputs.

    Earlier versions tightened collapse_threshold in steps and only truncated
    after multiple passes. In practice the first pass already fits in this repo,
    so we keep the output identical while deleting the unused complexity. If the
    tree ever exceeds budget_lines, we hard-truncate with a marker line.
    """
    lines = render(CONFIG.collapse_threshold)
    if len(lines) > CONFIG.budget_lines:
        truncated = lines[: CONFIG.budget_lines - 1]
        truncated.append("… (auto-collapsed to stay under 250 lines)")
        return truncated
    return lines


for line in render_with_budget():
    print(line)
PY
