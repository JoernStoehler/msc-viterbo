"""Tests for counterexample-hko experiment.

Tests both the geometry generation and the output properties.
"""

import json
import math

import pytest

from viterbo.experiments.counterexample_hko.stage_build import (
    build_hko_facets,
    build_minimum_orbit,
    build_output,
    compute_capacity_volume_sys,
    polygon_edge_data,
    regular_polygon_vertices,
)


class TestPolygonGeometry:
    """Test polygon geometry utilities."""

    def test_regular_pentagon_has_5_vertices(self) -> None:
        verts = regular_polygon_vertices(5)
        assert len(verts) == 5

    def test_vertices_on_circle(self) -> None:
        """All vertices should be at distance circumradius from origin."""
        verts = regular_polygon_vertices(5, circumradius=1.5)
        for x, y in verts:
            dist = math.hypot(x, y)
            assert abs(dist - 1.5) < 1e-10

    def test_phase_rotates_vertices(self) -> None:
        """Phase should rotate all vertices."""
        v0 = regular_polygon_vertices(5, phase=0.0)
        v90 = regular_polygon_vertices(5, phase=math.pi / 2)
        # First vertex should be rotated by 90 degrees
        assert abs(v0[0][0] - v90[0][1]) < 1e-10  # x -> y
        assert abs(v0[0][1] + v90[0][0]) < 1e-10  # y -> -x

    def test_edge_normals_are_unit(self) -> None:
        """All edge normals should be unit vectors."""
        verts = regular_polygon_vertices(5)
        for nx, ny, h in polygon_edge_data(verts):
            norm = math.hypot(nx, ny)
            assert abs(norm - 1.0) < 1e-10

    def test_edge_heights_positive(self) -> None:
        """Heights should be positive for convex polygon with origin inside."""
        verts = regular_polygon_vertices(5)
        for nx, ny, h in polygon_edge_data(verts):
            assert h > 0


class TestHKOFacets:
    """Test H-rep generation for the pentagon product."""

    def test_facet_count(self) -> None:
        """Should have 10 facets: 5 from K, 5 from T."""
        facets = build_hko_facets()
        assert len(facets) == 10

    def test_k_facets_in_q_plane(self) -> None:
        """K facets should have normals only in q-plane."""
        facets = build_hko_facets()
        for f in facets[:5]:  # K0-K4
            assert f.label.startswith("K")
            assert f.normal[2] == 0.0  # p1 component
            assert f.normal[3] == 0.0  # p2 component
            norm = math.hypot(f.normal[0], f.normal[1])
            assert abs(norm - 1.0) < 1e-10

    def test_t_facets_in_p_plane(self) -> None:
        """T facets should have normals only in p-plane."""
        facets = build_hko_facets()
        for f in facets[5:]:  # T0-T4
            assert f.label.startswith("T")
            assert f.normal[0] == 0.0  # q1 component
            assert f.normal[1] == 0.0  # q2 component
            norm = math.hypot(f.normal[2], f.normal[3])
            assert abs(norm - 1.0) < 1e-10

    def test_all_heights_positive(self) -> None:
        """All facet heights should be positive."""
        facets = build_hko_facets()
        for f in facets:
            assert f.height > 0


class TestCapacityVolume:
    """Test capacity, volume, and systolic ratio computations."""

    def test_capacity_positive(self) -> None:
        cap, vol, sys = compute_capacity_volume_sys()
        assert cap > 0

    def test_volume_positive(self) -> None:
        cap, vol, sys = compute_capacity_volume_sys()
        assert vol > 0

    def test_systolic_ratio_formula(self) -> None:
        """Systolic ratio should equal c²/(2*vol)."""
        cap, vol, sys = compute_capacity_volume_sys()
        expected = cap * cap / (2 * vol)
        assert abs(sys - expected) < 1e-10

    def test_systolic_ratio_closed_form(self) -> None:
        """Systolic ratio should equal (√5 + 3)/5."""
        cap, vol, sys = compute_capacity_volume_sys()
        expected = (math.sqrt(5) + 3) / 5
        assert abs(sys - expected) < 1e-10

    def test_viterbo_violated(self) -> None:
        """Systolic ratio should be > 1 (counterexample)."""
        cap, vol, sys = compute_capacity_volume_sys()
        assert sys > 1.0


class TestMinimumOrbit:
    """Test minimum orbit construction.

    The minimum orbit is a 2-bounce T-billiard trajectory (HK&O 2024).
    In 4D, this corresponds to a 4-segment orbit alternating K and T facets.
    """

    def test_orbit_is_closed(self) -> None:
        """First and last breakpoints should be equal."""
        facets = build_hko_facets()
        cap, _, _ = compute_capacity_volume_sys()
        orbit = build_minimum_orbit(facets, cap)
        bp = orbit["breakpoints"]
        assert bp[0] == bp[-1]

    def test_breaktimes_end_at_capacity(self) -> None:
        """Last breaktime should equal capacity."""
        facets = build_hko_facets()
        cap, _, _ = compute_capacity_volume_sys()
        orbit = build_minimum_orbit(facets, cap)
        assert abs(orbit["breaktimes"][-1] - cap) < 1e-10

    def test_breaktimes_strictly_increasing(self) -> None:
        """Breaktimes should be strictly increasing."""
        facets = build_hko_facets()
        cap, _, _ = compute_capacity_volume_sys()
        orbit = build_minimum_orbit(facets, cap)
        bt = orbit["breaktimes"]
        for i in range(len(bt) - 1):
            assert bt[i] < bt[i + 1]

    def test_is_4_segment_orbit(self) -> None:
        """2-bounce T-billiard = 4 segments in 4D (K-T-K-T)."""
        facets = build_hko_facets()
        cap, _, _ = compute_capacity_volume_sys()
        orbit = build_minimum_orbit(facets, cap)
        assert len(orbit["facet_sequence"]) == 4

    def test_alternates_k_and_t_facets(self) -> None:
        """Orbit should alternate between K-facets and T-facets."""
        facets = build_hko_facets()
        cap, _, _ = compute_capacity_volume_sys()
        orbit = build_minimum_orbit(facets, cap)
        labels = orbit["facet_labels"]
        # Pattern: K, T, K, T
        assert labels[0].startswith("K")
        assert labels[1].startswith("T")
        assert labels[2].startswith("K")
        assert labels[3].startswith("T")

    def test_hits_diagonal_k_facets(self) -> None:
        """Should hit K_0 and K_2 (diagonal pair)."""
        facets = build_hko_facets()
        cap, _, _ = compute_capacity_volume_sys()
        orbit = build_minimum_orbit(facets, cap)
        k_facets = [l for l in orbit["facet_labels"] if l.startswith("K")]
        assert "K0" in k_facets
        assert "K2" in k_facets

    def test_breakpoints_count(self) -> None:
        """Should have n+1 breakpoints for n segments (including closure)."""
        facets = build_hko_facets()
        cap, _, _ = compute_capacity_volume_sys()
        orbit = build_minimum_orbit(facets, cap)
        # 4 segments -> 5 breakpoints (last equals first)
        assert len(orbit["breakpoints"]) == len(orbit["facet_sequence"]) + 1

    def test_breakpoints_in_valid_range(self) -> None:
        """All breakpoint coordinates should be within the polytope bounds."""
        facets = build_hko_facets()
        cap, _, _ = compute_capacity_volume_sys()
        orbit = build_minimum_orbit(facets, cap)
        for bp in orbit["breakpoints"]:
            # Circumradius is 1, so all coords should be in [-1, 1]
            for coord in bp:
                assert -1.1 < coord < 1.1  # Small tolerance


class TestOutputFormat:
    """Test the complete JSON output structure."""

    def test_output_has_required_keys(self) -> None:
        """Output should have all required top-level keys."""
        data = build_output()
        required = [
            "name",
            "source",
            "convention",
            "polytope",
            "hrep",
            "capacity",
            "capacity_exact",
            "volume",
            "volume_exact",
            "systolic_ratio",
            "systolic_ratio_exact",
            "viterbo_conjecture_violated",
            "minimum_orbit",
        ]
        for key in required:
            assert key in data, f"Missing key: {key}"

    def test_exact_values_are_latex(self) -> None:
        """*_exact fields should contain LaTeX strings."""
        data = build_output()
        # Check they contain LaTeX-like content
        assert "\\" in data["capacity_exact"]  # Contains LaTeX command
        assert "\\" in data["volume_exact"]
        assert "\\" in data["systolic_ratio_exact"]

    def test_viterbo_violated_is_true(self) -> None:
        """Should flag that Viterbo's conjecture is violated."""
        data = build_output()
        assert data["viterbo_conjecture_violated"] is True

    def test_json_serializable(self) -> None:
        """Output should be JSON serializable."""
        data = build_output()
        # Should not raise
        json_str = json.dumps(data)
        assert len(json_str) > 0

    def test_json_roundtrip(self) -> None:
        """Output should survive JSON roundtrip."""
        data = build_output()
        json_str = json.dumps(data)
        restored = json.loads(json_str)
        assert restored["capacity"] == data["capacity"]
        assert restored["systolic_ratio"] == data["systolic_ratio"]
        assert len(restored["hrep"]["facets"]) == 10


class TestIntegration:
    """Integration tests running the full pipeline."""

    def test_build_writes_json(self, tmp_path) -> None:
        """Build stage should write valid JSON file."""
        from viterbo.experiments.counterexample_hko import stage_build

        # Temporarily override output path
        out_path = tmp_path / "hko2024.json"

        data = stage_build.build_output()
        with out_path.open("w", encoding="utf-8") as f:
            json.dump(data, f)

        assert out_path.exists()

        # Verify readable
        with out_path.open("r", encoding="utf-8") as f:
            loaded = json.load(f)

        assert loaded["name"] == "HK&O 2024 pentagon product"
        assert loaded["systolic_ratio"] > 1.0

    def test_plot_runs_without_error(self, tmp_path) -> None:
        """Plot stage should run without error given valid data."""
        from viterbo.experiments.counterexample_hko import stage_build, stage_plot

        # Create data file
        data_path = tmp_path / "hko2024.json"
        data = stage_build.build_output()
        with data_path.open("w", encoding="utf-8") as f:
            json.dump(data, f)

        # Run plot
        assets_dir = tmp_path / "assets"
        stage_plot.main(str(data_path), str(assets_dir))

        # Check output exists
        plot_path = assets_dir / "orbit-projections.png"
        assert plot_path.exists()
        assert plot_path.stat().st_size > 0  # Non-empty file
