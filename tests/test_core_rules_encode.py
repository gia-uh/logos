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
