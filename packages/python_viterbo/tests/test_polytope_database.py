"""Tests for polytope-database experiment.

Tests the staged pipeline: stage_polytopes, stage_volume, stage_capacity.
"""

import json
import math

import pytest

from viterbo.experiments.polytope_database.stage_capacity import (
    add_capacities,
    generate_stub_orbit,
)
from viterbo.experiments.polytope_database.stage_polytopes import (
    cell_24_hrep,
    cross_polytope_hrep,
    generate_polytopes,
    has_lagrangian_2face,
    is_lagrangian_product,
    simplex_hrep,
    tesseract_hrep,
)
from viterbo.experiments.polytope_database.stage_volume import add_volumes


class TestHRepGenerators:
    """Test H-rep generation for known polytopes."""

    def test_tesseract_has_8_facets(self) -> None:
        normals, heights = tesseract_hrep()
        assert len(normals) == 8
        assert len(heights) == 8

    def test_tesseract_normals_are_unit(self) -> None:
        normals, _ = tesseract_hrep()
        for n in normals:
            norm = math.sqrt(sum(x * x for x in n))
            assert abs(norm - 1.0) < 1e-10

    def test_tesseract_heights_positive(self) -> None:
        _, heights = tesseract_hrep()
        assert all(h > 0 for h in heights)

    def test_simplex_has_5_facets(self) -> None:
        normals, heights = simplex_hrep()
        assert len(normals) == 5
        assert len(heights) == 5

    def test_simplex_normals_are_unit(self) -> None:
        normals, _ = simplex_hrep()
        for n in normals:
            norm = math.sqrt(sum(x * x for x in n))
            assert abs(norm - 1.0) < 1e-10

    def test_cross_polytope_has_16_facets(self) -> None:
        normals, heights = cross_polytope_hrep()
        assert len(normals) == 16
        assert len(heights) == 16

    def test_cross_polytope_normals_are_unit(self) -> None:
        normals, _ = cross_polytope_hrep()
        for n in normals:
            norm = math.sqrt(sum(x * x for x in n))
            assert abs(norm - 1.0) < 1e-10

    def test_24_cell_has_24_facets(self) -> None:
        normals, heights = cell_24_hrep()
        assert len(normals) == 24
        assert len(heights) == 24

    def test_24_cell_normals_are_unit(self) -> None:
        normals, _ = cell_24_hrep()
        for n in normals:
            norm = math.sqrt(sum(x * x for x in n))
            assert abs(norm - 1.0) < 1e-10


class TestLagrangianDetection:
    """Test Lagrangian product and 2-face detection."""

    def test_tesseract_is_lagrangian_product(self) -> None:
        """Tesseract [-1,1]^4 = [-1,1]^2 x [-1,1]^2 is a Lagrangian product."""
        normals, _ = tesseract_hrep()
        assert is_lagrangian_product(normals)

    def test_simplex_not_lagrangian_product(self) -> None:
        """4-simplex is not a Lagrangian product."""
        normals, _ = simplex_hrep()
        assert not is_lagrangian_product(normals)

    def test_cross_polytope_not_lagrangian_product(self) -> None:
        """Cross-polytope is not a Lagrangian product."""
        normals, _ = cross_polytope_hrep()
        assert not is_lagrangian_product(normals)

    def test_24_cell_not_lagrangian_product(self) -> None:
        """24-cell is not a Lagrangian product."""
        normals, _ = cell_24_hrep()
        assert not is_lagrangian_product(normals)

    def test_tesseract_has_lagrangian_2faces(self) -> None:
        """Tesseract has Lagrangian 2-faces (e.g., facets in same q or p plane)."""
        normals, _ = tesseract_hrep()
        assert has_lagrangian_2face(normals)

    def test_cross_polytope_has_some_lagrangian_2faces(self) -> None:
        """Cross-polytope has some Lagrangian 2-faces (despite being non-Lagrangian product)."""
        normals, _ = cross_polytope_hrep()
        # Has Lagrangian 2-faces, but still suitable for tube algorithm
        # (tube algorithm filters/handles these internally)
        assert has_lagrangian_2face(normals)

    def test_24_cell_has_some_lagrangian_2faces(self) -> None:
        """24-cell has some Lagrangian 2-faces (despite being non-Lagrangian product)."""
        normals, _ = cell_24_hrep()
        # Has Lagrangian 2-faces, but still suitable for tube algorithm
        assert has_lagrangian_2face(normals)


class TestOrbitGeneration:
    """Test stub orbit generation."""

    def test_orbit_is_closed(self) -> None:
        normals, _ = tesseract_hrep()
        bp, bt, fs = generate_stub_orbit(normals, capacity=4.0, seed=42)
        assert bp[0] == bp[-1], "Orbit must be closed"

    def test_breaktimes_strictly_increasing(self) -> None:
        normals, _ = tesseract_hrep()
        bp, bt, fs = generate_stub_orbit(normals, capacity=4.0, seed=42)
        for i in range(len(bt) - 1):
            assert bt[i] < bt[i + 1], "Breaktimes must be strictly increasing"

    def test_breaktimes_end_at_capacity(self) -> None:
        normals, _ = tesseract_hrep()
        capacity = 4.0
        bp, bt, fs = generate_stub_orbit(normals, capacity=capacity, seed=42)
        assert abs(bt[-1] - capacity) < 1e-10

    def test_facet_sequence_length(self) -> None:
        normals, _ = tesseract_hrep()
        bp, bt, fs = generate_stub_orbit(normals, capacity=4.0, seed=42)
        assert len(fs) == len(bp) - 1

    def test_no_duplicate_facets(self) -> None:
        normals, _ = tesseract_hrep()
        bp, bt, fs = generate_stub_orbit(normals, capacity=4.0, seed=42)
        assert len(fs) == len(set(fs)), "No facet should appear twice"


class TestStagePolytopes:
    """Test stage 1: polytope generation."""

    def test_generates_all_families(self) -> None:
        polytopes = generate_polytopes()
        families = {p["family"] for p in polytopes}
        expected = {"tesseract", "simplex", "cross-polytope", "24-cell", "random"}
        assert families == expected

    def test_generates_12_polytopes(self) -> None:
        """4 named + 8 random = 12 total."""
        polytopes = generate_polytopes()
        assert len(polytopes) == 12

    def test_all_have_required_keys(self) -> None:
        polytopes = generate_polytopes()
        required_keys = {
            "id",
            "family",
            "facet_count",
            "normals",
            "heights",
            "has_lagrangian_2face",
            "is_lagrangian_product",
        }
        for p in polytopes:
            assert set(p.keys()) == required_keys

    def test_no_capacity_or_volume(self) -> None:
        """Stage 1 should not include capacity or volume."""
        polytopes = generate_polytopes()
        for p in polytopes:
            assert "capacity" not in p
            assert "volume" not in p

    def test_tesseract_properties(self) -> None:
        polytopes = generate_polytopes()
        tess = next(p for p in polytopes if p["id"] == "tesseract")
        assert tess["facet_count"] == 8
        assert tess["is_lagrangian_product"]
        assert tess["has_lagrangian_2face"]

    def test_cross_polytope_properties(self) -> None:
        polytopes = generate_polytopes()
        cross = next(p for p in polytopes if p["id"] == "cross-polytope")
        assert cross["facet_count"] == 16
        assert not cross["is_lagrangian_product"]
        assert cross["has_lagrangian_2face"]  # Has some Lagrangian 2-faces

    def test_24_cell_properties(self) -> None:
        polytopes = generate_polytopes()
        cell = next(p for p in polytopes if p["id"] == "24-cell")
        assert cell["facet_count"] == 24
        assert not cell["is_lagrangian_product"]
        assert cell["has_lagrangian_2face"]  # Has some Lagrangian 2-faces


class TestStageVolume:
    """Test stage 2: volume addition."""

    def test_adds_volume_to_all(self) -> None:
        polytopes = generate_polytopes()
        polytopes_with_vol = add_volumes(polytopes)
        assert all("volume" in p for p in polytopes_with_vol)

    def test_preserves_existing_keys(self) -> None:
        polytopes = generate_polytopes()
        original_keys = set(polytopes[0].keys())
        polytopes_with_vol = add_volumes(polytopes)
        new_keys = set(polytopes_with_vol[0].keys())
        assert original_keys.issubset(new_keys)
        assert "volume" in new_keys

    def test_tesseract_volume(self) -> None:
        polytopes = [
            {
                "id": "tesseract",
                "normals": [[1, 0, 0, 0]],
                "heights": [1],
                "facet_count": 8,
                "family": "tesseract",
                "has_lagrangian_2face": True,
                "is_lagrangian_product": True,
            }
        ]
        polytopes_with_vol = add_volumes(polytopes)
        assert polytopes_with_vol[0]["volume"] == 16.0


class TestStageCapacity:
    """Test stage 3: capacity addition."""

    def test_adds_capacity_fields(self) -> None:
        polytopes = generate_polytopes()
        polytopes = add_volumes(polytopes)
        polytopes = add_capacities(polytopes)

        for p in polytopes:
            assert "capacity" in p
            assert "systolic_ratio" in p
            assert "orbit_breakpoints" in p
            assert "orbit_breaktimes" in p
            assert "orbit_facet_sequence" in p

    def test_systolic_ratio_formula(self) -> None:
        polytopes = generate_polytopes()
        polytopes = add_volumes(polytopes)
        polytopes = add_capacities(polytopes)

        for p in polytopes:
            expected_ratio = p["capacity"] ** 2 / (2 * p["volume"])
            assert abs(p["systolic_ratio"] - expected_ratio) < 1e-10

    def test_tesseract_capacity(self) -> None:
        polytopes = generate_polytopes()
        polytopes = add_volumes(polytopes)
        polytopes = add_capacities(polytopes)
        tess = next(p for p in polytopes if p["id"] == "tesseract")
        assert tess["capacity"] == 4.0


class TestFullPipeline:
    """Test the complete staged pipeline."""

    def test_pipeline_produces_complete_data(self) -> None:
        # Stage 1: polytopes
        polytopes = generate_polytopes()
        assert len(polytopes) == 12

        # Stage 2: volumes
        polytopes = add_volumes(polytopes)
        assert all("volume" in p for p in polytopes)

        # Stage 3: capacities
        polytopes = add_capacities(polytopes)
        assert all("capacity" in p for p in polytopes)
        assert all("systolic_ratio" in p for p in polytopes)

    def test_json_serializable(self) -> None:
        """Ensure all output is JSON-serializable."""
        polytopes = generate_polytopes()
        polytopes = add_volumes(polytopes)
        polytopes = add_capacities(polytopes)

        # Should not raise
        json_str = json.dumps(polytopes)
        assert isinstance(json_str, str)

    def test_orbit_invariants(self) -> None:
        """Verify orbit data satisfies invariants."""
        polytopes = generate_polytopes()
        polytopes = add_volumes(polytopes)
        polytopes = add_capacities(polytopes)

        for p in polytopes:
            # Orbit closed
            assert p["orbit_breakpoints"][0] == p["orbit_breakpoints"][-1]

            # Breaktimes strictly increasing
            bt = p["orbit_breaktimes"]
            for i in range(len(bt) - 1):
                assert bt[i] < bt[i + 1]

            # Final breaktime equals capacity
            assert abs(bt[-1] - p["capacity"]) < 1e-10

            # Facet sequence length matches
            assert len(p["orbit_facet_sequence"]) == len(p["orbit_breakpoints"]) - 1

            # No duplicate facets
            fs = p["orbit_facet_sequence"]
            assert len(fs) == len(set(fs))
