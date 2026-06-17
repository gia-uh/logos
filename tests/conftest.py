# tests/conftest.py
import pytest
from logos.expr import Var

@pytest.fixture
def x(): return Var("x", int)
@pytest.fixture
def y(): return Var("y", int)
@pytest.fixture
def z(): return Var("z", int)
