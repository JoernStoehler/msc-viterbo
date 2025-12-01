#!/usr/bin/env python3
r"""Lightweight math/markup lint for thesis Markdown.

Checks:
- forbid raw `$` math delimiters outside code fences;
- check counts of `\(`/`\)` and `\[`/`\]` per file (imbalances are warnings→fail).
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "docs"
BAD = []
DOLLAR_RE = re.compile(r"(?<!\\)\$")  # unescaped $


def lint_file(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    in_code = False
    dollar_hits = []
    for lineno, line in enumerate(lines, start=1):
        stripped = line.strip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            in_code = not in_code
            continue
        if in_code:
            continue
        if DOLLAR_RE.search(line):
            dollar_hits.append(lineno)
    left_inline = text.count(r"\(")
    right_inline = text.count(r"\)")
    left_display = text.count(r"\[")
    right_display = text.count(r"\]")

    if dollar_hits:
        BAD.append(f"{path}: raw $ on lines {', '.join(map(str, dollar_hits))}")
    if left_inline != right_inline:
        BAD.append(
            f"{path}: unmatched \\( / \\) count ({left_inline} vs {right_inline})"
        )
    if left_display != right_display:
        BAD.append(
            f"{path}: unmatched \\[ / \\] count ({left_display} vs {right_display})"
        )


def main() -> int:
    md_files = sorted(ROOT.rglob("*.md"))
    for path in md_files:
        lint_file(path)
    if BAD:
        print("lint_math: FAIL")
        for item in BAD:
            print(f"- {item}")
        return 1
    print("lint_math: OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
