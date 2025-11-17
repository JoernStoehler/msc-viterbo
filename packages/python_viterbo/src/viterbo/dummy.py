"""Placeholder helpers so the Python toolchain can be smoke-tested."""

from __future__ import annotations

from typing import Iterable

__all__ = ["greet", "alternating_sum"]


def greet(name: str) -> str:
    """Return a cheerful greeting with basic normalisation."""
    target = name.strip() or "friend"
    return f"Hello, {target.title()}!"


def alternating_sum(values: Iterable[int]) -> int:
    """Compute a simple alternating sum (a0 - a1 + a2 - ...)."""
    total = 0
    for index, value in enumerate(values):
        total += value if index % 2 == 0 else -value
    return total
