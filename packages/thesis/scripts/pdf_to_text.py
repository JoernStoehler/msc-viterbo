#!/usr/bin/env python3
"""
Minimal PDF → text extractor for quick citation/equation lookup.

Usage:
  uv run --with pypdf scripts/pdf_to_text.py input.pdf [output.txt]

No dependencies beyond `pypdf` (pulled on the fly when using `uv run --with`).
When no output path is given, the text is printed to stdout.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


def extract_text(pdf_path: Path) -> str:
    from pypdf import PdfReader

    reader = PdfReader(str(pdf_path))
    chunks = []
    for page in reader.pages:
        # `extract_text` may return None on image-only pages; guard against it.
        page_text = page.extract_text() or ""
        chunks.append(page_text)
    return "\n\n".join(chunks)


def main() -> None:
    parser = argparse.ArgumentParser(description="Extract text from a PDF (best-effort).")
    parser.add_argument("pdf", type=Path, help="Path to the PDF file")
    parser.add_argument("output", nargs="?", type=Path, help="Optional path for the extracted text")
    args = parser.parse_args()

    if not args.pdf.is_file():
        parser.error(f"PDF not found: {args.pdf}")

    text = extract_text(args.pdf)

    if args.output:
        args.output.write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
