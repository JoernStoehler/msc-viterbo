"""Path helpers for experiment data and assets.

Centralizes path computation so experiments don't need fragile parent traversal.
"""

from pathlib import Path

# This file: packages/python_viterbo/src/viterbo/paths.py
# 3 parents up = packages/python_viterbo/
_PYTHON_PKG = Path(__file__).parent.parent.parent


def get_data_dir(experiment: str) -> Path:
    """Get the data directory for an experiment.

    Args:
        experiment: Experiment label (e.g., "algorithm_inventory")

    Returns:
        Path to packages/python_viterbo/data/<experiment>/
    """
    return _PYTHON_PKG / "data" / experiment


def get_assets_dir(experiment: str) -> Path:
    """Get the LaTeX assets directory for an experiment.

    Args:
        experiment: Experiment label (e.g., "algorithm_inventory")

    Returns:
        Path to packages/latex_viterbo/assets/<experiment>/
    """
    return _PYTHON_PKG.parent / "latex_viterbo" / "assets" / experiment
