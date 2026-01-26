"""Tests for polytope-database experiment.

Tests both the stub data generation and the invariants.
"""

import math

import pandas as pd
import pytest

from viterbo.experiments.polytope_database.stage_build import (
    build_stub_dataframe,
    generate_stub_orbit,
    has_lagrangian_2face,
    is_lagrangian_product,
    simplex_hrep,
    tesseract_hrep,
    validate_invariants,
)


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

    def test_tesseract_has_lagrangian_2faces(self) -> None:
        """Tesseract has Lagrangian 2-faces (e.g., facets in same q or p plane)."""
        normals, _ = tesseract_hrep()
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


class TestDataFrameBuild:
    """Test full DataFrame construction."""

    def test_build_succeeds(self) -> None:
        df = build_stub_dataframe()
        assert isinstance(df, pd.DataFrame)
        assert len(df) == 10  # tesseract + simplex + 8 random

    def test_has_expected_columns(self) -> None:
        df = build_stub_dataframe()
        expected = {
            "id",
            "family",
            "facet_count",
            "normals",
            "heights",
            "capacity",
            "volume",
            "systolic_ratio",
            "orbit_breakpoints",
            "orbit_breaktimes",
            "orbit_facet_sequence",
            "has_lagrangian_2face",
            "is_lagrangian_product",
        }
        assert set(df.columns) == expected

    def test_invariants_hold(self) -> None:
        df = build_stub_dataframe()
        # Should not raise
        validate_invariants(df)

    def test_tesseract_values(self) -> None:
        df = build_stub_dataframe()
        tess = df[df["id"] == "tesseract"].iloc[0]
        assert tess["capacity"] == 4.0
        assert tess["volume"] == 16.0
        assert abs(tess["systolic_ratio"] - 0.5) < 1e-10

    def test_simplex_capacity(self) -> None:
        df = build_stub_dataframe()
        simp = df[df["id"] == "simplex"].iloc[0]
        assert simp["capacity"] == 0.25


class TestParquetRoundtrip:
    """Test Parquet serialization."""

    def test_roundtrip(self, tmp_path) -> None:
        df = build_stub_dataframe()
        path = tmp_path / "test.parquet"
        df.to_parquet(path, index=False)

        df2 = pd.read_parquet(path)
        assert len(df2) == len(df)
        assert list(df2.columns) == list(df.columns)

        # Check nested data survives
        tess = df2[df2["id"] == "tesseract"].iloc[0]
        assert len(tess["normals"]) == 8
        assert len(tess["orbit_breakpoints"]) > 0
