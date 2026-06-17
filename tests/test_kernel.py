# tests/test_kernel.py
import pytest
from logos.expr import Var, Lit, Add, Eq as LogosEq, And, Or, Implies, Forall, ForallNode
from logos.helpers import structural_eq
from logos.kernel import (
    Context, KernelError, infer, check,
    Refl, Symm, Trans, Subst, Axiom,
    ForallIntro, ForallElim,
    ImpliesIntro, ImpliesElim,
    AndIntro, AndElimL, AndElimR,
    OrIntroL, OrIntroR,
    HypRef,
)

def test_refl(x):
    ctx = Context({}, {})
    term = Refl(x)
    result = infer(term, ctx)
    assert structural_eq(result, x == x)

def test_symm(x, y):
    ctx = Context({"h": x == y}, {})
    term = Symm(Axiom("h"))
    result = infer(term, ctx)
    assert structural_eq(result, y == x)

def test_trans(x, y, z):
    ctx = Context({"h1": x == y, "h2": y == z}, {})
    term = Trans(Axiom("h1"), Axiom("h2"))
    result = infer(term, ctx)
    assert structural_eq(result, x == z)

def test_trans_middle_mismatch(x, y, z):
    ctx = Context({"h1": x == y, "h2": z == x}, {})  # y ≠ z
    with pytest.raises(KernelError, match="middle"):
        infer(Trans(Axiom("h1"), Axiom("h2")), ctx)

def test_subst(x, y):
    ctx = Context({"h": x == y}, {})
    # Subst(h, f) where f(e) = e + Lit(1): proves (x+1) == (y+1)
    term = Subst(Axiom("h"), lambda e: e + Lit(1))
    result = infer(term, ctx)
    assert structural_eq(result, (x + Lit(1)) == (y + Lit(1)))

def test_forall_intro_elim(x, y):
    # ForallIntro(x, Refl(x)) proves Forall(x, x == x)
    ctx = Context({}, {})
    intro_term = ForallIntro(x, Refl(x))
    stmt = infer(intro_term, ctx)
    assert structural_eq(stmt, Forall(x, x == x))

    # ForallElim on that proof with y: proves y == y
    elim_term = ForallElim(intro_term, y)
    result = infer(elim_term, ctx)
    assert structural_eq(result, y == y)

def test_implies_intro_elim(x):
    # ImpliesIntro(antecedent, "h", HypRef("h")) where h: x > 0 proves (x > 0) >> (x > 0)
    ctx = Context({}, {})
    antecedent = x > Lit(0)
    intro = ImpliesIntro(antecedent, "h", HypRef("h"))
    stmt = infer(intro, ctx)
    assert structural_eq(stmt, antecedent >> antecedent)

def test_check_fails_on_mismatch(x, y):
    ctx = Context({}, {})
    term = Refl(x)
    with pytest.raises(KernelError):
        check(term, x == y, ctx)  # Refl(x) proves x==x, not x==y

def test_hyp_ref(x):
    ctx = Context({}, {"my_hyp": x > Lit(0)})
    term = HypRef("my_hyp")
    result = infer(term, ctx)
    assert structural_eq(result, x > Lit(0))

def test_and_intro(x, y):
    ctx = Context({"hx": x > Lit(0), "hy": y > Lit(0)}, {})
    term = AndIntro(Axiom("hx"), Axiom("hy"))
    result = infer(term, ctx)
    assert structural_eq(result, (x > Lit(0)) & (y > Lit(0)))
