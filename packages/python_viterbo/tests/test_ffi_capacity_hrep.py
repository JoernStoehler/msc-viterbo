"""Tests for FFI capacity algorithms.

Tests the Rust-Python bindings for EHZ capacity computation.
"""

from __future__ import annotations

from typing import Any

import pytest

try:
    import rust_viterbo_ffi as ffi
except ImportError:
    ffi: Any = None


@pytest.fixture(autouse=True)
def require_ffi_installed() -> None:
    if ffi is None:
        pytest.skip(
            "rust_viterbo_ffi is not installed. Build it with: "
            "cd packages/python_viterbo && uv run maturin develop --manifest-path ../rust_viterbo/ffi/Cargo.toml"
        )


# ============================================================================
# Test Fixtures
# ============================================================================


def tesseract_hrep() -> tuple[list[list[float]], list[float]]:
    """Return the tesseract [-1,1]^4 as H-rep."""
    normals = [
        [1.0, 0.0, 0.0, 0.0],
        [-1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, -1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, -1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
        [0.0, 0.0, 0.0, -1.0],
    ]
    heights = [1.0] * 8
    return normals, heights


def simplex_hrep() -> tuple[list[list[float]], list[float]]:
    """Return a 4D simplex as H-rep (5 facets)."""
    normals = [
        [1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
        [-0.5, -0.5, -0.5, -0.5],
    ]
    heights = [1.0] * 5
    return normals, heights


# ============================================================================
# HK2017 Algorithm Tests
# ============================================================================


def test_hk2017_tesseract_capacity() -> None:
    """HK2017 should compute capacity=4 for tesseract [-1,1]^4."""
    normals, heights = tesseract_hrep()
    result = ffi.hk2017_capacity_hrep(normals, heights)

    assert hasattr(result, "capacity")
    assert abs(result.capacity - 4.0) < 1e-6, f"Expected 4.0, got {result.capacity}"
    assert result.permutations_evaluated > 0


def test_hk2017_simplex_runs() -> None:
    """HK2017 should run on a 5-facet simplex."""
    normals, heights = simplex_hrep()
    result = ffi.hk2017_capacity_hrep(normals, heights)

    assert result.capacity > 0
    assert len(result.optimal_permutation) > 0
    assert len(result.optimal_beta) > 0


def test_hk2017_graph_pruning() -> None:
    """HK2017 with graph pruning should give same result but fewer evaluations."""
    normals, heights = tesseract_hrep()

    result_naive = ffi.hk2017_capacity_hrep(normals, heights, use_graph_pruning=False)
    result_pruned = ffi.hk2017_capacity_hrep(normals, heights, use_graph_pruning=True)

    assert abs(result_naive.capacity - result_pruned.capacity) < 1e-9
    # Graph pruning should evaluate fewer permutations
    assert result_pruned.permutations_evaluated <= result_naive.permutations_evaluated


def test_hk2017_result_repr() -> None:
    """Hk2017Result should have a readable repr."""
    normals, heights = tesseract_hrep()
    result = ffi.hk2017_capacity_hrep(normals, heights)

    repr_str = repr(result)
    assert "Hk2017Result" in repr_str
    assert "capacity=" in repr_str


# ============================================================================
# symplectic_form_4d Tests
# ============================================================================


def test_symplectic_form_basic() -> None:
    """symplectic_form_4d computes omega(a, b) correctly."""
    # omega((1,0,0,0), (0,0,1,0)) = 1*1 - 0 = 1
    result = ffi.symplectic_form_4d([1.0, 0.0, 0.0, 0.0], [0.0, 0.0, 1.0, 0.0])
    assert abs(result - 1.0) < 1e-9


def test_symplectic_form_antisymmetric() -> None:
    """symplectic_form_4d is antisymmetric: omega(a, b) = -omega(b, a)."""
    a = [1.0, 2.0, 3.0, 4.0]
    b = [5.0, 6.0, 7.0, 8.0]
    assert abs(ffi.symplectic_form_4d(a, b) + ffi.symplectic_form_4d(b, a)) < 1e-9


def test_symplectic_form_zero_self() -> None:
    """symplectic_form_4d(a, a) = 0 for any vector a."""
    a = [1.0, 2.0, 3.0, 4.0]
    assert abs(ffi.symplectic_form_4d(a, a)) < 1e-9


# ============================================================================
# Error Handling Tests
# ============================================================================


def test_hk2017_invalid_mismatched_lengths() -> None:
    """HK2017 should reject mismatched normals/heights lengths."""
    normals = [[1.0, 0.0, 0.0, 0.0], [-1.0, 0.0, 0.0, 0.0]]
    heights = [1.0]  # Only one height for two normals

    with pytest.raises(ValueError, match="Invalid polytope"):
        ffi.hk2017_capacity_hrep(normals, heights)
