"""
Colocated tests for stage_2.

Run: cd experiments && uv run pytest _example/test_stage_2.py
"""

import importlib.util
import sys
from pathlib import Path

# Load stage_2 module from same directory
_stage_2_path = Path(__file__).parent / "stage_2.py"
_spec = importlib.util.spec_from_file_location("stage_2", _stage_2_path)
stage_2 = importlib.util.module_from_spec(_spec)
sys.modules["stage_2"] = stage_2
_spec.loader.exec_module(stage_2)

CONFIG = stage_2.CONFIG
main = stage_2.main


def test_config_has_required_keys():
    """CONFIG must have experiment_name and variant."""
    assert "experiment_name" in CONFIG
    assert "variant" in CONFIG


def test_main_creates_figure(tmp_path, monkeypatch):
    """main() should create figure.png."""
    # Create fake input file
    input_dir = tmp_path / "input"
    input_dir.mkdir()
    (input_dir / "stage_1_output.txt").write_text("test input")

    # Set up output directory
    assets_dir = tmp_path / "assets"

    monkeypatch.setattr(stage_2, "INPUT_DIR", input_dir)
    monkeypatch.setattr(stage_2, "ASSETS_DIR", assets_dir)

    main()

    output_file = assets_dir / "figure.png"
    assert output_file.exists()
    # Check it's a valid PNG (starts with PNG magic bytes)
    content = output_file.read_bytes()
    assert content[:8] == b"\x89PNG\r\n\x1a\n"
