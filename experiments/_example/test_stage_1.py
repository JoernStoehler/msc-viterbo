"""
Colocated tests for stage_1.

Run: cd experiments && uv run pytest _example/test_stage_1.py
"""

import importlib.util
import sys
from pathlib import Path

# Load stage_1 module from same directory
_stage_1_path = Path(__file__).parent / "stage_1.py"
_spec = importlib.util.spec_from_file_location("stage_1", _stage_1_path)
stage_1 = importlib.util.module_from_spec(_spec)
sys.modules["stage_1"] = stage_1
_spec.loader.exec_module(stage_1)

CONFIG = stage_1.CONFIG
main = stage_1.main


def test_config_has_required_keys():
    """CONFIG must have experiment_name and variant."""
    assert "experiment_name" in CONFIG
    assert "variant" in CONFIG


def test_main_creates_output(tmp_path, monkeypatch):
    """main() should create output file."""
    monkeypatch.setattr(stage_1, "OUTPUT_DIR", tmp_path)

    main()

    output_file = tmp_path / "stage_1_output.txt"
    assert output_file.exists()
    content = output_file.read_text()
    assert "_example" in content
