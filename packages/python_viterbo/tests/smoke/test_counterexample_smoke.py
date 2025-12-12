from pathlib import Path

from viterbo.experiments.counterexample_hko import stage_build


def test_counterexample_files_exist() -> None:
    # Ensure the generated dataset files are present (built in repo by stage_build)
    assert stage_build.DATA_DIR.joinpath("facets.json").exists()
    assert stage_build.DATA_DIR.joinpath("summary.json").exists()
    assert stage_build.ASSET_DIR.joinpath("polygons.png").exists()


def test_capacity_formula_positive() -> None:
    cap, vol, sys = stage_build.capacity_values()
    assert cap > 0 and vol > 0 and sys > 1
