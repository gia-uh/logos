# tests/test_integration.py
import pytest
from logos.expr import Var, Lit, Forall
from logos.registry import clear_axioms, get_all_axioms
from logos.theorem import theorem, prove, LogosProofError
from logos.tactics.arithmetic import ring, linarith
from logos.tactics.structural import intro, assumption, split
import logos.builtins


def setup_function():
    clear_axioms()
    # builtins module is already imported; call _load() directly to re-register
    # after clear_axioms() wiped the registry
    logos.builtins._load()


@pytest.fixture
def x():
    return Var("x", int)


@pytest.fixture
def y():
    return Var("y", int)


def test_prove_add_comm(x, y):
    stmt = Forall(x, y, x + y == y + x)
    proof = prove(stmt, [intro("x", "y"), ring()])
    assert proof is not None


def test_theorem_registers_as_axiom(x, y):
    stmt = Forall(x, y, x + y == y + x)
    theorem("add_comm_test", stmt, [intro("x", "y"), ring()])
    assert "add_comm_test" in get_all_axioms()


def test_theorem_raises_on_invalid_proof(x, y):
    stmt = Forall(x, y, x + y == x - y)  # false
    with pytest.raises(LogosProofError):
        theorem("bogus", stmt, [intro("x", "y"), ring()])


def test_theorem_does_not_register_on_failure(x, y):
    stmt = Forall(x, y, x + y == x - y)
    with pytest.raises(LogosProofError):
        theorem("bogus2", stmt, [intro("x", "y"), ring()])
    assert "bogus2" not in get_all_axioms()


def test_prove_linarith(x):
    stmt = Forall(x, (x > Lit(0)) >> (x + Lit(1) > Lit(0)))
    proof = prove(stmt, [
        intro("x", "h"),
        linarith(),
    ])
    assert proof is not None


def test_builtins_loaded():
    axioms = get_all_axioms()
    assert "int_add_comm" in axioms
    assert "int_mul_comm" in axioms
    assert "int_distrib" in axioms


def test_prove_returns_proof_term(x, y):
    from logos.kernel import ProofTerm
    stmt = Forall(x, y, x + y == y + x)
    proof = prove(stmt, [intro("x", "y"), ring()])
    assert isinstance(proof, ProofTerm)


def test_theorem_returns_proof_term(x, y):
    from logos.kernel import ProofTerm
    stmt = Forall(x, y, x * y == y * x)
    result = theorem("mul_comm_test", stmt, [intro("x", "y"), ring()])
    assert isinstance(result, ProofTerm)


def test_prove_empty_proof_raises(x):
    stmt = x + Lit(1) == Lit(1) + x
    with pytest.raises(LogosProofError):
        prove(stmt, [])


def test_prove_wrong_tactic_raises(x, y):
    # ring() on an inequality — should fail
    stmt = Forall(x, y, x + y == y + x)
    with pytest.raises(LogosProofError):
        prove(stmt, [ring()])  # ring() on Forall, not Eq
