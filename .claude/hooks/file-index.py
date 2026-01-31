#!/usr/bin/env python3
"""
Generates a file tree for agent context at session startup.

Uses blacklist approach: shows everything except explicitly excluded patterns.
Shows `<N files omitted>` when truncating so agents know listing is incomplete.
"""
from __future__ import annotations

import sys
from pathlib import Path
from types import SimpleNamespace

HELP = """\
Usage: file-index.py [--help]

Prints a compact file tree for agent context.
Uses blacklist approach: shows everything except excluded patterns.

Edit CONFIG in this script to adjust blacklist and display rules.
"""

CONFIG = SimpleNamespace(
    # Directories to completely skip (never show)
    blacklist_dirs={
        ".git",
        ".venv",
        "target",
        "build",
        "dist",
        "node_modules",
        "__pycache__",
        ".pytest_cache",
        ".mypy_cache",
        ".ruff_cache",
        ".ipynb_checkpoints",
        ".latexmk",
        "site",
        "site-packages",
    },
    # Prefixes for directories to skip
    blacklist_prefixes={"_minted"},
    # File extensions to skip
    blacklist_extensions={".pyc", ".pyo"},
    # Maximum depth to show
    depth_limit=5,
    # Maximum total lines before truncating
    budget_lines=200,
)


def should_skip(path: Path, name: str) -> bool:
    """Check if a path should be skipped based on blacklist rules."""
    if name in CONFIG.blacklist_dirs:
        return True
    if any(name.startswith(pfx) for pfx in CONFIG.blacklist_prefixes):
        return True
    if path.is_file() and path.suffix in CONFIG.blacklist_extensions:
        return True
    return False


def count_omitted(root: Path, rel: Path) -> int:
    """Count files that would be shown if we descended further."""
    count = 0
    base = root / rel
    if not base.is_dir():
        return 0
    try:
        for p in base.rglob("*"):
            if p.is_symlink():
                continue
            if should_skip(p, p.name):
                continue
            if p.is_file():
                count += 1
    except PermissionError:
        pass
    return count


def list_children(root: Path, rel: Path) -> list[tuple[Path, bool]]:
    """List children of a directory, sorted (dirs first, then by name)."""
    base = root / rel
    children = []
    try:
        for p in sorted(base.iterdir(), key=lambda x: (not x.is_dir(), x.name.lower())):
            if p.is_symlink():
                continue
            if should_skip(p, p.name):
                continue
            child_rel = rel / p.name
            children.append((child_rel, p.is_dir()))
    except PermissionError:
        pass
    return children


def render_tree(root: Path) -> list[str]:
    """Render the file tree as a list of lines."""
    lines: list[str] = []
    total_omitted = 0

    def walk(rel: Path, prefix: str, last: bool, depth: int) -> None:
        nonlocal total_omitted

        abs_path = root / rel
        is_dir = abs_path.is_dir()
        label = rel.name + ("/" if is_dir else "")
        connector = "\u2514\u2500\u2500 " if last else "\u251c\u2500\u2500 "

        # Check if we should collapse due to depth limit
        at_depth_limit = depth >= CONFIG.depth_limit and is_dir

        if at_depth_limit:
            omitted = count_omitted(root, rel)
            if omitted > 0:
                total_omitted += omitted
                lines.append(f"{prefix}{connector}{label} <{omitted} files omitted>")
            else:
                lines.append(f"{prefix}{connector}{label} (empty)")
            return

        # Check if directory is empty
        kids = list_children(root, rel) if is_dir else []
        if is_dir and not kids:
            lines.append(f"{prefix}{connector}{label} (empty)")
            return

        lines.append(f"{prefix}{connector}{label}")

        if not is_dir:
            return

        new_prefix = prefix + ("    " if last else "\u2502   ")
        for idx, (child_rel, _) in enumerate(kids):
            walk(child_rel, new_prefix, idx == len(kids) - 1, depth + 1)

    lines.append(".")
    top_children = list_children(root, Path("."))
    for idx, (rel, _) in enumerate(top_children):
        walk(rel, "", idx == len(top_children) - 1, 1)

    # Truncate if over budget
    if len(lines) > CONFIG.budget_lines:
        lines = lines[: CONFIG.budget_lines - 1]
        lines.append(f"... <truncated, {len(lines)} lines shown>")

    return lines


def main() -> int:
    if len(sys.argv) > 1:
        if sys.argv[1] in ("--help", "-h"):
            print(HELP)
            return 0
        print(f"Unknown flag: {sys.argv[1]}", file=sys.stderr)
        return 1

    root = Path.cwd().resolve()

    print("[File Index] Repository structure")
    print()
    for line in render_tree(root):
        print(line)

    return 0


if __name__ == "__main__":
    sys.exit(main())
