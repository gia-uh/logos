# tests/conftest.py
import atexit
import os
import shutil
import tempfile

import pytest

from logos.expr import Var


def pytest_configure(config):
    """Keep the suite away from the user's persistent evidence cache."""
    if os.environ.get("LOGOS_CACHE_DIR") is None:
        directory = tempfile.mkdtemp(prefix="logos-evidence-pytest-")
        os.environ["LOGOS_CACHE_DIR"] = directory
        atexit.register(shutil.rmtree, directory, True)


@pytest.fixture
def x(): return Var("x", int)
@pytest.fixture
def y(): return Var("y", int)
@pytest.fixture
def z(): return Var("z", int)
