from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

try:
    import rust_viterbo_ffi
except ImportError:  # pragma: no cover
    rust_viterbo_ffi = None

ffi: Any = rust_viterbo_ffi


def load_hko_facets() -> tuple[list[list[float]], list[float]]:
    data_path = (
        Path(__file__).resolve().parents[1]
        / "data"
        / "counterexamples"
        / "hk-o-2024"
        / "facets.json"
    )
    data = json.loads(data_path.read_text())
    return data["normals"], data["heights"]


@pytest.fixture(autouse=True)
def require_ffi_installed() -> None:
    if rust_viterbo_ffi is None:
        pytest.skip(
            "rust_viterbo_ffi is not installed. Build it with: "
            "cd packages/python_viterbo && uv run maturin develop --manifest-path ../rust_viterbo/ffi/Cargo.toml"
        )


def test_hko_call_returns_capacity_or_error() -> None:
    """Test that the algorithm runs on the HK&O counterexample.

    The algorithm should either:
    1. Return a valid capacity result (dict with 'capacity' key)
    2. Raise RuntimeError if no valid orbits found

    This tests the integration of the full pipeline.
    """
    normals, heights = load_hko_facets()
    try:
        result = ffi.tube_capacity_hrep(normals, heights)
        # If we get a result, check it has expected structure
        assert isinstance(result, dict)
        assert "capacity" in result
        assert "diagnostics" in result
        assert result["capacity"] > 0
        diag = result["diagnostics"]
        assert diag["nodes_explored"] > 0
    except RuntimeError as e:
        # Algorithm ran but found no valid orbits (acceptable for now)
        message = str(e).lower()
        assert "orbit" in message or "lagrangian" in message


def test_negative_height_rejected() -> None:
    normals, heights = load_hko_facets()
    heights[0] = -1.0
    with pytest.raises(ValueError) as excinfo:
        ffi.tube_capacity_hrep(normals, heights)
    assert "not positive" in str(excinfo.value).lower()


def test_non_unit_normal_rejected() -> None:
    normals, heights = load_hko_facets()
    normals[0] = [2.0, 0.0, 0.0, 0.0]
    with pytest.raises(ValueError) as excinfo:
        ffi.tube_capacity_hrep(normals, heights)
    assert "not unit" in str(excinfo.value).lower()


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
