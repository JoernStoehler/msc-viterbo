from __future__ import annotations

import json
from pathlib import Path

import pytest

import rust_viterbo_ffi  # pyright: ignore[reportMissingImports]


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


def test_hko_call_returns_not_implemented_with_metadata() -> None:
    normals, heights = load_hko_facets()
    with pytest.raises(NotImplementedError) as excinfo:
        rust_viterbo_ffi.tube_capacity_hrep(
            normals, heights, eps_lagr=1e-9, eps_perturb=1e-6, seed=42
        )
    message = str(excinfo.value).lower()
    assert "lagrangian" in message
    assert "perturbation" in message


def test_negative_height_rejected() -> None:
    normals, heights = load_hko_facets()
    heights[0] = -1.0
    with pytest.raises(ValueError) as excinfo:
        rust_viterbo_ffi.tube_capacity_hrep(normals, heights)
    assert "not positive" in str(excinfo.value).lower()


def test_non_unit_normal_rejected() -> None:
    normals, heights = load_hko_facets()
    normals[0] = [2.0, 0.0, 0.0, 0.0]
    with pytest.raises(ValueError) as excinfo:
        rust_viterbo_ffi.tube_capacity_hrep(normals, heights)
    assert "not unit" in str(excinfo.value).lower()
