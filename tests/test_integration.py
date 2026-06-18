# tests/test_integration.py
import pytest
import logos
import logos.tactics as t
import logos.builtins as builtins
from logos.theorem import LogosProofError
from logos.tactics.arithmetic import ring, linarith
from logos.tactics.structural import intro, assumption, split


def test_prove_add_comm():
    @logos.theorem
    def add_comm(x: int, y: int):
        return x + y == y + x

    logos.check(add_comm.proof(intro("x", "y"), ring()))
    assert add_comm.certified


def test_theorem_certified_after_check():
    @logos.theorem
    def mul_comm(x: int, y: int):
        return x * y == y * x

    assert not mul_comm.certified
    logos.check(mul_comm.proof(intro("x", "y"), ring()))
    assert mul_comm.certified


def test_theorem_raises_on_invalid_proof():
    @logos.theorem
    def bogus(x: int, y: int):
        return x + y == x - y  # false

    with pytest.raises(LogosProofError):
        logos.check(bogus.proof(intro("x", "y"), ring()))


def test_theorem_not_certified_on_failure():
    @logos.theorem
    def bogus2(x: int, y: int):
        return x + y == x - y

    with pytest.raises(LogosProofError):
        logos.check(bogus2.proof(intro("x", "y"), ring()))
    assert not bogus2.certified


def test_prove_linarith():
    @logos.theorem
    def pos_plus_one(x: int):
        return (x > logos.lit(0)) >> (x + logos.lit(1) > logos.lit(0))

    logos.check(pos_plus_one.proof(intro("x", "h"), linarith()))
    assert pos_plus_one.certified


def test_builtins_are_axiom_objects():
    assert isinstance(builtins.int_add_comm, logos.Axiom)
    assert isinstance(builtins.int_mul_comm, logos.Axiom)
    assert isinstance(builtins.int_distrib, logos.Axiom)
    assert builtins.int_add_comm.certified


def test_check_returns_theorem():
    @logos.theorem
    def x_eq_x(x: int):
        return x == x

    result = logos.check(x_eq_x.proof(intro("x"), t.refl()))
    assert result is x_eq_x


def test_check_idempotent():
    @logos.theorem
    def add_zero(x: int):
        return x + logos.lit(0) == x

    logos.check(add_zero.proof(intro("x"), ring()))
    # calling check again on a certified theorem is a no-op
    logos.check(add_zero)
    assert add_zero.certified


def test_prove_empty_proof_raises():
    from logos.expr import Var, Lit
    x = logos.var("x", int)
    stmt = x + logos.lit(1) == logos.lit(1) + x
    gp = logos.prove(stmt, [])
    with pytest.raises(LogosProofError):
        logos.check(gp)


def test_prove_wrong_tactic_raises():
    @logos.theorem
    def comm(x: int, y: int):
        return x + y == y + x

    with pytest.raises(LogosProofError):
        logos.check(comm.proof(ring()))  # ring() on Forall, not Eq


# --- Public API integration tests ---

def test_full_double_proof():
    @logos.define
    def double(v: int):
        return v + v

    @logos.theorem
    def double_eq_2x(v: int):
        return double(v) == logos.lit(2) * v

    logos.check(double_eq_2x.proof(t.intro("v"), t.unfold(double), t.ring()))
    assert double_eq_2x.certified


def test_full_abs_nonneg():
    @logos.theorem
    def zero_plus_zero(v: int):
        return v + logos.lit(0) == v

    logos.check(zero_plus_zero.proof(t.intro("v"), t.ring()))
    assert zero_plus_zero.certified


def test_proof_decorator_style():
    @logos.theorem
    def comm2(x: int, y: int):
        return x + y == y + x

    @comm2.proof
    def _():
        return [t.intro("x", "y"), t.ring()]

    logos.check(comm2)
    assert comm2.certified


def test_ground_proof():
    gp = logos.prove(logos.lit(1) + logos.lit(2) == logos.lit(3), [t.norm_num()])
    logos.check(gp)
    assert gp.certified


def test_theorem_no_proof_raises():
    @logos.theorem
    def unproved(x: int):
        return x == x

    with pytest.raises(LogosProofError):
        logos.check(unproved)
