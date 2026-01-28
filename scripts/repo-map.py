#!/usr/bin/env python3
"""
Prints a compact repo map: pwd, git status, and file tree.

Run this when you need to understand the project structure.
The tree auto-collapses large directories and hides build artifacts.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from types import SimpleNamespace

HELP = """\
Usage: scripts/repo-map.py

Prints pwd, git status (porcelain v2), and a compact repo tree.
Use this to get an overview of the project structure.

The tree auto-collapses large directories and hides build artifacts.
Edit CONFIG in this script to adjust skip/hide/collapse rules.
"""

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
    skip_prefixes={"_minted"},
    hide_names={
        "__pycache__",
        ".pytest_cache",
        ".mypy_cache",
        ".ruff_cache",
        ".ipynb_checkpoints",
    },
    collapse_threshold=120,
    budget_lines=250,
    depth_limit=5,
)


def main() -> int:
    if len(sys.argv) > 1:
        if sys.argv[1] in ("--help", "-h"):
            print(HELP)
            return 0
        print(f"Unknown flag: {sys.argv[1]}", file=sys.stderr)
        return 1

    root = Path.cwd().resolve()

    print("[repo-map] pwd")
    print(root)

    print("[repo-map] git status --porcelain=v2 -b")
    result = subprocess.run(
        ["git", "status", "--porcelain=v2", "-b"],
        capture_output=True,
        text=True,
    )
    print(result.stdout, end="")
    if result.stderr:
        print(result.stderr, end="", file=sys.stderr)

    print("[repo-map] file tree")
    print(root)
    for line in render_tree(root):
        print(line)

    return 0


# -------------------------- tree rendering -----------------------------


def is_must_show(rel: Path) -> bool:
    return rel in CONFIG.must_show


def is_skip(rel: Path) -> bool:
    name = rel.name
    if name in CONFIG.skip_names:
        return True
    if any(name.startswith(pfx) for pfx in CONFIG.skip_prefixes):
        return True
    return False


def list_children(root: Path, rel: Path) -> list[tuple[Path, bool]]:
    base = root / rel
    children = []
    for p in sorted(base.iterdir(), key=lambda x: (not x.is_dir(), x.name.lower())):
        name = p.name
        if name in CONFIG.hide_names:
            continue
        if p.is_symlink():
            continue
        child_rel = rel / name
        children.append((child_rel, p.is_dir()))
    return children


def descendant_count(root: Path, rel: Path, threshold: int | None) -> tuple[int, int]:
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


def should_collapse(root: Path, rel: Path, depth: int, threshold: int | None) -> bool:
    abs_path = root / rel
    if not abs_path.is_dir():
        return False
    if is_skip(rel):
        return True
    if is_must_show(rel):
        return False
    if depth > CONFIG.depth_limit:
        return True
    if threshold:
        files, dirs = descendant_count(root, rel, threshold)
        if files + dirs > threshold:
            return True
    return False


def render_tree(root: Path) -> list[str]:
    lines: list[str] = []
    threshold = CONFIG.collapse_threshold

    def walk(rel: Path, prefix: str, last: bool, depth: int) -> None:
        abs_path = root / rel
        is_dir = abs_path.is_dir()
        label = rel.name + ("/" if is_dir else "")
        collapsed = should_collapse(root, rel, depth, threshold)

        empty = is_dir and not collapsed and not list_children(root, rel)
        connector = "\u2514\u2500\u2500 " if last else "\u251c\u2500\u2500 "
        if empty:
            suffix = " (empty)"
        elif collapsed:
            suffix = " (collapsed)"
        else:
            suffix = ""

        lines.append(f"{prefix}{connector}{label}{suffix}")

        if collapsed or empty or not is_dir:
            return

        new_prefix = prefix + ("    " if last else "\u2502   ")
        kids = list_children(root, rel)
        for idx, (child_rel, _) in enumerate(kids):
            walk(child_rel, new_prefix, idx == len(kids) - 1, depth + 1)

    lines.append(".")
    top_children = list_children(root, Path("."))
    for idx, (rel, _) in enumerate(top_children):
        walk(rel, "", idx == len(top_children) - 1, 1)

    if len(lines) > CONFIG.budget_lines:
        lines = lines[: CONFIG.budget_lines - 1]
        lines.append("... (auto-collapsed to stay under 250 lines)")

    return lines


if __name__ == "__main__":
    sys.exit(main())
