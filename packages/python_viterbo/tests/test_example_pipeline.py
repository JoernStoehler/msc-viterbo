"""Tests for example-pipeline experiment.

This test file demonstrates:
- Testing individual functions
- Testing stage outputs
- Using tmp_path for isolated test runs
"""

import json

import pytest

from viterbo.experiments.example_pipeline.stage_analyze import analyze, sum_of_squares
from viterbo.experiments.example_pipeline.stage_build import generate_data


class TestStageBuild:
    """Tests for stage_build functions."""

    def test_generate_data_returns_correct_size(self) -> None:
        data = generate_data(100, seed=42)
        assert len(data) == 100

    def test_generate_data_is_reproducible(self) -> None:
        data1 = generate_data(10, seed=42)
        data2 = generate_data(10, seed=42)
        assert data1 == data2

    def test_generate_data_different_seeds_differ(self) -> None:
        data1 = generate_data(10, seed=42)
        data2 = generate_data(10, seed=43)
        assert data1 != data2

    def test_generate_data_values_in_range(self) -> None:
        data = generate_data(1000, seed=42)
        assert all(0 <= x < 1 for x in data)


class TestStageAnalyze:
    """Tests for stage_analyze functions."""

    def test_sum_of_squares_empty(self) -> None:
        assert sum_of_squares([]) == 0

    def test_sum_of_squares_known_values(self) -> None:
        # 1^2 + 2^2 + 3^2 = 1 + 4 + 9 = 14
        assert sum_of_squares([1.0, 2.0, 3.0]) == 14.0

    def test_analyze_returns_expected_keys(self) -> None:
        datasets = {"10": [0.1] * 10}
        results = analyze(datasets)
        assert "10" in results
        assert "size" in results["10"]
        assert "sum_of_squares" in results["10"]
        assert "sos_per_element" in results["10"]


class TestIntegration:
    """Integration tests running stages in sequence."""

    def test_full_pipeline(self, tmp_path) -> None:
        """Run build -> analyze and verify outputs."""
        from viterbo.experiments.example_pipeline import stage_analyze, stage_build

        # Create config
        config = {"seed": 42, "sizes": [10, 100], "output_dir": str(tmp_path)}
        config_path = tmp_path / "config.json"
        with config_path.open("w") as f:
            json.dump(config, f)

        # Run build
        stage_build.main(str(config_path))
        assert (tmp_path / "synthetic_data.json").exists()

        # Run analyze
        stage_analyze.main(str(tmp_path))
        assert (tmp_path / "results.json").exists()

        # Verify results
        with (tmp_path / "results.json").open() as f:
            results = json.load(f)
        assert "10" in results
        assert "100" in results
        assert results["10"]["size"] == 10
        assert results["100"]["size"] == 100
