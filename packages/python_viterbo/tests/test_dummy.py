"""Smoke-tests for the placeholder helper functions."""

from viterbo import alternating_sum, greet


def test_greet_normalises_whitespace() -> None:
    assert greet("  alice  ") == "Hello, Alice!"
    assert greet("") == "Hello, Friend!"


def test_alternating_sum_handles_iterables() -> None:
    assert alternating_sum([1, 2, 3, 4]) == -2
    assert alternating_sum(range(5)) == 2
