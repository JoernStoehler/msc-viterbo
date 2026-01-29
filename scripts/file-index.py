#!/usr/bin/env python3
"""
Generates a compressed file index for agent context.

Unlike repo-map.py (detailed tree for exploration), this produces a compact
index (~20-30 lines) suitable for passive context in CLAUDE.md or startup hooks.

Format inspired by Vercel's AGENTS.md approach: group files by directory,
use brace expansion notation, omit boilerplate.
"""
from __future__ import annotations

import sys
from pathlib import Path


def get_files(base: Path, pattern: str = "**/*") -> list[Path]:
    """Get all files matching pattern, excluding hidden/build dirs."""
    skip = {".git", ".venv", "target", "build", "dist", "__pycache__",
            ".pytest_cache", ".mypy_cache", ".ruff_cache", "site", ".latexmk"}
    files = []
    for p in base.glob(pattern):
        if p.is_file() and not any(s in p.parts for s in skip):
            files.append(p.relative_to(base))
    return sorted(files)


def compress_names(names: list[str], ext: str) -> str:
    """Compress ['foo.rs', 'bar.rs'] -> '{foo,bar}.rs'"""
    if not names:
        return ""
    stems = [n.removesuffix(ext) for n in names]
    if len(stems) == 1:
        return names[0]
    return "{" + ",".join(stems) + "}" + ext


def group_by_dir(files: list[Path]) -> dict[Path, list[str]]:
    """Group files by parent directory."""
    groups: dict[Path, list[str]] = {}
    for f in files:
        parent = f.parent
        groups.setdefault(parent, []).append(f.name)
    return groups


def format_rust_crate(crate_path: Path, base: Path) -> list[str]:
    """Format a Rust crate's structure compactly."""
    lines = []
    src = crate_path / "src"
    tests = crate_path / "tests"

    if src.exists():
        files = get_files(src, "**/*.rs")
        groups = group_by_dir(files)

        parts = []
        for dir_path, names in sorted(groups.items()):
            compressed = compress_names(names, ".rs")
            if dir_path == Path("."):
                parts.append(compressed)
            else:
                parts.append(f"{dir_path}/{compressed}")

        if parts:
            rel_crate = crate_path.relative_to(base)
            lines.append(f"  {rel_crate}/src: " + " | ".join(parts))

    if tests.exists():
        test_files = get_files(tests, "*.rs")
        if test_files:
            compressed = compress_names([f.name for f in test_files], ".rs")
            rel_crate = crate_path.relative_to(base)
            lines.append(f"  {rel_crate}/tests: {compressed}")

    return lines


def format_python_package(pkg_path: Path, base: Path) -> list[str]:
    """Format a Python package's structure compactly."""
    lines = []
    src = pkg_path / "src" / "viterbo"

    if src.exists():
        files = get_files(src, "*.py")
        if files:
            compressed = compress_names([f.name for f in files], ".py")
            rel = pkg_path.relative_to(base)
            lines.append(f"  {rel}/src/viterbo: {compressed}")

    return lines


def format_latex_package(pkg_path: Path, base: Path) -> list[str]:
    """Format LaTeX chapters compactly."""
    lines = []
    chapters = pkg_path / "chapters"

    if chapters.exists():
        files = get_files(chapters, "*.tex")
        groups = group_by_dir(files)

        parts = []
        for dir_path, names in sorted(groups.items()):
            compressed = compress_names(names, ".tex")
            if dir_path == Path("."):
                parts.append(compressed)
            else:
                parts.append(f"{dir_path}/{compressed}")

        if parts:
            rel = pkg_path.relative_to(base)
            lines.append(f"  {rel}/chapters: " + " | ".join(parts))

    return lines


def format_skills(skills_path: Path, base: Path) -> str:
    """Format skills directory compactly."""
    if not skills_path.exists():
        return ""

    skill_dirs = sorted(d.name for d in skills_path.iterdir() if d.is_dir())
    if not skill_dirs:
        return ""

    return f"  .claude/skills: {{{','.join(skill_dirs)}}}/SKILL.md"


def format_docs(docs_path: Path, base: Path) -> list[str]:
    """Format docs directory."""
    lines = []

    conventions = docs_path / "conventions"
    if conventions.exists():
        files = get_files(conventions, "*.md")
        if files:
            compressed = compress_names([f.name for f in files], ".md")
            lines.append(f"  docs/conventions: {compressed}")

    papers = docs_path / "papers"
    if papers.exists():
        readme = papers / "README.md"
        if readme.exists():
            lines.append("  docs/papers: README.md (index of papers)")

    notes = docs_path / "notes"
    if notes.exists():
        files = get_files(notes, "*.md")
        if files:
            names = [f.name for f in files]
            lines.append(f"  docs/notes: {', '.join(names)}")

    return lines


def main() -> int:
    root = Path.cwd().resolve()

    # Header
    print("[File Index] Compressed repo structure for agent context")
    print()

    # Rust workspace
    rust_base = root / "packages" / "rust_viterbo"
    if rust_base.exists():
        print("Rust (packages/rust_viterbo):")
        for crate in ["geom", "hk2017", "tube", "ffi"]:
            crate_path = rust_base / crate
            if crate_path.exists():
                for line in format_rust_crate(crate_path, root):
                    print(line)
        print()

    # Python package
    python_base = root / "packages" / "python_viterbo"
    if python_base.exists():
        print("Python (packages/python_viterbo):")
        for line in format_python_package(python_base, root):
            print(line)
        print()

    # LaTeX
    latex_base = root / "packages" / "latex_viterbo"
    if latex_base.exists():
        print("LaTeX (packages/latex_viterbo):")
        for line in format_latex_package(latex_base, root):
            print(line)
        print()

    # Skills
    skills_path = root / ".claude" / "skills"
    skill_line = format_skills(skills_path, root)
    if skill_line:
        print("Skills:")
        print(skill_line)
        print()

    # Docs
    docs_path = root / "docs"
    if docs_path.exists():
        doc_lines = format_docs(docs_path, root)
        if doc_lines:
            print("Docs:")
            for line in doc_lines:
                print(line)
            print()

    # Key top-level files
    print("Config: CLAUDE.md, .claude/settings.json, msc-viterbo.code-workspace")

    return 0


if __name__ == "__main__":
    sys.exit(main())
