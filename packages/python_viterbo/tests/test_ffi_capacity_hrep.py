from __future__ import annotations

import math
from typing import Any

import pytest

try:
    import rust_viterbo_ffi
except ImportError:  # pragma: no cover
    rust_viterbo_ffi = None

ffi: Any = rust_viterbo_ffi


@pytest.fixture(autouse=True)
def require_ffi_installed() -> None:
    if rust_viterbo_ffi is None:
        pytest.skip(
            "rust_viterbo_ffi is not installed. Build it with: "
            "cd packages/python_viterbo && uv run maturin develop --manifest-path ../rust_viterbo/ffi/Cargo.toml"
        )


# ============================================================================
# Minkowski Billiard Algorithm Tests
# ============================================================================


def tesseract_hrep() -> tuple[list[list[float]], list[float]]:
    """Return the tesseract [-1,1]^4 as a Lagrangian product."""
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


def test_billiard_tesseract_capacity() -> None:
    """Billiard algorithm should compute capacity=4 for tesseract."""
    normals, heights = tesseract_hrep()
    result = ffi.billiard_capacity_hrep(normals, heights)

    assert isinstance(result, dict)
    assert abs(result["capacity"] - 4.0) < 1e-6, f"Expected 4.0, got {result['capacity']}"
    assert result["witness"] is not None
    assert len(result["witness"]["breakpoints"]) == 4


def test_billiard_rejects_non_lagrangian() -> None:
    """Billiard algorithm should reject non-Lagrangian products."""
    # A polytope with a mixed facet (not a Lagrangian product)
    normals = [
        [1.0, 0.0, 0.0, 0.0],
        [-1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, -1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, -1.0, 0.0],
        [0.5, 0.0, 0.5, 0.0],  # Mixed q-p facet (after normalization)
        [-0.5, 0.0, -0.5, 0.0],
    ]
    # Normalize
    import math

    for n in normals[6:8]:
        norm = math.sqrt(sum(x**2 for x in n))
        for i in range(4):
            n[i] /= norm

    heights = [1.0] * 8

    with pytest.raises(ValueError) as excinfo:
        ffi.billiard_capacity_hrep(normals, heights)
    assert "lagrangian" in str(excinfo.value).lower()


# ============================================================================
# HK2019 Algorithm Tests
# ============================================================================


def test_hk2019_simplex_runs() -> None:
    """HK2019 should run on a 5-facet simplex (5! = 120 permutations)."""
    normals = [
        [1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
        [-0.5, -0.5, -0.5, -0.5],
    ]
    heights = [1.0] * 5

    result = ffi.hk2019_capacity_hrep(normals, heights)
    assert isinstance(result, dict)
    assert result["capacity"] > 0
    assert result["diagnostics"]["nodes_explored"] == 120  # 5!


def test_hk2019_rejects_large_polytope() -> None:
    """HK2019 should reject polytopes with >10 facets."""
    # 12-facet polytope
    normals = [
        [1.0, 0.0, 0.0, 0.0],
        [-1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, -1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, -1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
        [0.0, 0.0, 0.0, -1.0],
        [0.5, 0.5, 0.5, 0.5],
        [-0.5, -0.5, 0.5, 0.5],
        [0.5, -0.5, 0.5, -0.5],
        [-0.5, 0.5, -0.5, 0.5],
    ]
    heights = [1.0] * 12

    with pytest.raises(ValueError) as excinfo:
        ffi.hk2019_capacity_hrep(normals, heights)
    assert "10" in str(excinfo.value) and "12" in str(excinfo.value)
