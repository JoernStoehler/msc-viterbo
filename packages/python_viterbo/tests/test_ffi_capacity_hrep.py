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
# HK2017 Algorithm Tests (the main, working algorithm)
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


def test_hk2017_tesseract_capacity() -> None:
    """HK2017 should compute capacity=4 for tesseract [-1,1]^4."""
    normals, heights = tesseract_hrep()
    result = ffi.hk2017_capacity_hrep(normals, heights)

    assert hasattr(result, "capacity")
    assert abs(result.capacity - 4.0) < 1e-6, f"Expected 4.0, got {result.capacity}"
    assert result.permutations_evaluated > 0


def test_hk2017_simplex_runs() -> None:
    """HK2017 should run on a 5-facet simplex."""
    normals = [
        [1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
        [-0.5, -0.5, -0.5, -0.5],
    ]
    heights = [1.0] * 5

    result = ffi.hk2017_capacity_hrep(normals, heights)
    assert result.capacity > 0


def test_hk2017_graph_pruning() -> None:
    """HK2017 with graph pruning should give same result but fewer evaluations."""
    normals, heights = tesseract_hrep()

    result_naive = ffi.hk2017_capacity_hrep(normals, heights, use_graph_pruning=False)
    result_pruned = ffi.hk2017_capacity_hrep(normals, heights, use_graph_pruning=True)

    assert abs(result_naive.capacity - result_pruned.capacity) < 1e-9
    # Graph pruning should evaluate fewer permutations
    assert result_pruned.permutations_evaluated <= result_naive.permutations_evaluated


# ============================================================================
# Legacy API Tests
# ============================================================================


def test_hk2019_legacy_api() -> None:
    """hk2019_capacity_hrep is a legacy alias that returns just float."""
    normals, heights = tesseract_hrep()
    result = ffi.hk2019_capacity_hrep(normals, heights)

    # Legacy API returns float, not object
    assert isinstance(result, float)
    assert abs(result - 4.0) < 1e-6


# ============================================================================
# Archived Function Tests
# ============================================================================


def test_billiard_archived() -> None:
    """billiard_capacity_hrep is archived and raises NotImplementedError."""
    normals, heights = tesseract_hrep()
    with pytest.raises(NotImplementedError):
        ffi.billiard_capacity_hrep(normals, heights)


def test_tube_archived() -> None:
    """tube_capacity_hrep is archived and raises NotImplementedError."""
    normals, heights = tesseract_hrep()
    with pytest.raises(NotImplementedError):
        ffi.tube_capacity_hrep(normals, heights)


# ============================================================================
# Utility Function Tests
# ============================================================================


def test_symplectic_form() -> None:
    """symplectic_form_4d computes omega(a, b) correctly."""
    # omega((1,0,0,0), (0,0,1,0)) = 1*1 - 0 = 1
    result = ffi.symplectic_form_4d([1.0, 0.0, 0.0, 0.0], [0.0, 0.0, 1.0, 0.0])
    assert abs(result - 1.0) < 1e-9

    # omega is antisymmetric
    a = [1.0, 2.0, 3.0, 4.0]
    b = [5.0, 6.0, 7.0, 8.0]
    assert abs(ffi.symplectic_form_4d(a, b) + ffi.symplectic_form_4d(b, a)) < 1e-9
