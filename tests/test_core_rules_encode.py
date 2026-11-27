"""Encoding tests for rules that only Rust can verify."""
import json

from logos.expr import And, Eq, Exists, Forall, Implies, Lit, Lt, Not, Var
from logos.kernel import (
    AndIntro, CoreLaw, ExistsIntro, ForallIntro, ImpliesIntro, Induction, Least, Refl,
)
from logos.portable import artifact_bytes, statement_declarations


def encode(statement, evidence):
    artifact = artifact_bytes("t", statement, statement_declarations(statement), evidence)
    return json.loads(artifact)


def test_induction_uses_the_checker_field_names():
    n = Var("n", int)
    statement = Forall(n, Implies(Not(Lt(n, Lit(0))), Eq(n, n)))
    k = Var("n", int)
    step = ForallIntro(
        k,
        ImpliesIntro(
            Not(Lt(k, Lit(0))),
            "lower",
            ImpliesIntro(Eq(k, k), "previous", Refl(k + Lit(1))),
        ),
    )
    data = encode(statement, Induction(Lit(0), n, Eq(n, n), Refl(Lit(0)), step))
    proof = data["proof"]
    assert proof["tag"] == "induction"
    assert set(proof) == {"tag", "bound", "name", "predicate", "base", "step"}
    assert proof["predicate"]["tag"] == "eq"


def test_least_uses_the_checker_field_names():
    m = Var("m", int)
    predicate = Eq(m, Lit(5))
    membership = And(Not(Lt(m, Lit(5))), predicate)
    k = Var("k", int)
    statement = Exists(
        m,
        And(
            membership,
            Forall(
                k,
                Implies(And(Not(Lt(k, Lit(5))), Lt(k, m)), Not(predicate)),
            ),
        ),
    )
    nonempty = ExistsIntro(
        Lit(5),
        AndIntro(CoreLaw("lt_irrefl", (Lit(5),)), Refl(Lit(5))),
        Exists(m, membership),
    )
    data = encode(statement, Least(Lit(5), m, predicate, nonempty))
    proof = data["proof"]
    assert proof["tag"] == "least"
    assert set(proof) == {"tag", "bound", "name", "predicate", "nonempty"}


def test_recursor_uses_the_checker_field_names():
    import logos
    from logos.kernel import RecursorBase

    fact = logos.recursor("fact_enc", 1, lambda n, previous: (n + 1) * previous)
    data = encode(Eq(fact(Lit(0)), Lit(1)), RecursorBase(fact))
    declaration = data["functions"][0]
    assert declaration["recursor"]["base"] == {"tag": "int", "value": "1"}
    assert declaration["recursor"]["step"]["tag"] == "mul"
    assert data["proof"] == {"tag": "recursor_base", "id": declaration["id"]}


def test_recursor_equations_infer_in_the_kernel():
    import logos
    from logos.expr import Add, App, Mul
    from logos.helpers import structural_eq
    from logos.kernel import Context, HypRef, RecursorBase, RecursorStep, infer

    fact = logos.recursor("fact_inf", 1, lambda n, previous: (n + 1) * previous)
    zero = Lit(0)
    one = Lit(1)
    applied_zero = App(fact.name, [zero], fact)
    assert structural_eq(
        infer(RecursorBase(fact), Context({}, {})),
        Eq(applied_zero, one),
    )
    context = Context({}, {"nonneg": Not(Lt(zero, zero))})
    result = infer(RecursorStep(fact, zero, HypRef("nonneg")), context)
    assert structural_eq(
        result,
        Eq(
            App(fact.name, [Add(zero, one)], fact),
            Mul(Add(zero, one), applied_zero),
        ),
    )
