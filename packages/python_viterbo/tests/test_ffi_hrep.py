from __future__ import annotations

import json
from pathlib import Path

import pytest
import rust_viterbo_ffi  # type: ignore[reportMissingImports]

DATA_DIR = (
    Path(__file__).resolve().parents[1] / "data" / "counterexamples" / "hk-o-2024"
)


def load_hko_facets() -> tuple[list[list[float]], list[float]]:
    data = json.loads((DATA_DIR / "facets.json").read_text())
    return data["normals"], data["heights"]


def test_capacity_hrep_reports_not_implemented_with_diagnostics() -> None:
    normals, heights = load_hko_facets()
    with pytest.raises(NotImplementedError) as excinfo:
        rust_viterbo_ffi.capacity_hrep(
            normals, heights, eps_lagr=1.0e-8, eps_perturb=1.0e-6, seed=7
        )
    message = str(excinfo.value)
    assert "tube algorithm not implemented" in message
    assert "lagrangian_detected=" in message
    assert "perturbed_count=" in message


def test_capacity_hrep_rejects_bad_shape() -> None:
    with pytest.raises(ValueError) as excinfo:
        rust_viterbo_ffi.capacity_hrep([[1.0, 0.0, 0.0]], [1.0])
    assert "expected 4" in str(excinfo.value)


def test_capacity_hrep_rejects_negative_height() -> None:
    with pytest.raises(ValueError) as excinfo:
        rust_viterbo_ffi.capacity_hrep([[1.0, 0.0, 0.0, 0.0]], [-1.0])
    assert "not positive" in str(excinfo.value)


def test_capacity_hrep_rejects_non_unit_normal() -> None:
    with pytest.raises(ValueError) as excinfo:
        rust_viterbo_ffi.capacity_hrep([[2.0, 0.0, 0.0, 0.0]], [1.0])
    assert "not unit" in str(excinfo.value)
