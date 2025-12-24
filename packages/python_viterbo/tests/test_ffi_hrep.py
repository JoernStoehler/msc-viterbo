from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

import rust_viterbo_ffi  # type: ignore[reportMissingImports]

ffi: Any = rust_viterbo_ffi

DATA_PATH = (
    Path(__file__).resolve().parents[1]
    / "data"
    / "counterexamples"
    / "hk-o-2024"
    / "facets.json"
)


def load_hko_facets() -> tuple[list[list[float]], list[float]]:
    data = json.loads(DATA_PATH.read_text())
    return data["normals"], data["heights"]


def test_capacity_hrep_returns_not_implemented_with_metadata() -> None:
    normals, heights = load_hko_facets()
    with pytest.raises(NotImplementedError) as excinfo:
        ffi.capacity_hrep(
            normals, heights, eps_lagr=1e-12, eps_perturb=1e-6, seed=7, unit_tol=1e-8
        )
    message = str(excinfo.value)
    assert "lagrangian_detected=true" in message
    assert "perturbed_count" in message


def test_capacity_hrep_rejects_bad_shape() -> None:
    normals = [[1.0, 0.0, 0.0]]
    heights = [1.0]
    with pytest.raises(ValueError) as excinfo:
        ffi.capacity_hrep(normals, heights)
    assert "expected 4" in str(excinfo.value)


def test_capacity_hrep_rejects_negative_height() -> None:
    normals = [[1.0, 0.0, 0.0, 0.0]]
    heights = [-0.5]
    with pytest.raises(ValueError) as excinfo:
        ffi.capacity_hrep(normals, heights)
    assert "HeightNonPositive" in str(excinfo.value)


def test_capacity_hrep_rejects_non_unit_normal() -> None:
    normals = [[2.0, 0.0, 0.0, 0.0]]
    heights = [1.0]
    with pytest.raises(ValueError) as excinfo:
        ffi.capacity_hrep(normals, heights, unit_tol=1e-8)
    assert "NormalNonUnit" in str(excinfo.value)
