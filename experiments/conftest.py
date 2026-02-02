# Shared pytest fixtures for experiments
# Add fixtures here that are useful across multiple experiments

import pytest


@pytest.fixture
def data_dir(tmp_path):
    """Temporary directory for test data outputs."""
    return tmp_path / "data"
