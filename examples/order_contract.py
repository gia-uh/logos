"""Prove the minimum of two integers one branch at a time.

Install the wheel and put the Rust checker on PATH, then from the repository
root run:

    python examples/order_contract.py
    logos check --strict minimum_then.logos
    logos check --strict minimum_else.logos
    logos check --strict lt_add_transport.logos
    logos check --strict lt_neq_from_lt.logos

The source fragment is one ``if``/``else`` over ``<`` with one ``return`` per
branch. Each theorem supplies a ``requires=`` that selects one path: ``x < y``
selects the then branch and ``~(x < y)`` selects the else branch, so the
equality boundary ``x == y`` belongs to the else path.

The last two theorems prove genuine order consequences from an explicit
assumption. They cite the checker-owned core laws ``lt_add`` and ``lt_neq``;
no custom axiom is involved.
"""
import logos
from logos import tactics as t


def minimum(x: int, y: int) -> int:
    if x < y:
        return x
    else:
        return y


@logos.theorem(about=minimum)
def minimum_then(x, y, *, result):
    return logos.contract(requires=(x < y), ensures=(result == x))


@logos.theorem(about=minimum)
def minimum_else(x, y, *, result):
    return logos.contract(requires=~(x < y), ensures=(result == y))


@logos.theorem
def lt_add_transport(x: int, y: int, c: int):
    return (x < y) >> ((x + c) < (y + c))


@logos.theorem
def lt_neq_from_lt(x: int, y: int):
    return (x < y) >> ~(x == y)


if __name__ == "__main__":
    minimum_then.check()
    minimum_else.check()
    logos.check(lt_add_transport.proof(t.intro("x", "y", "c", "h"), t.order("lt_add")))
    logos.check(lt_neq_from_lt.proof(t.intro("x", "y", "h"), t.order("lt_neq")))
    for theorem in (minimum_then, minimum_else, lt_add_transport, lt_neq_from_lt):
        logos.export_proof(theorem, f"{theorem.name}.logos")
        print(theorem.statement)
    print(
        "wrote minimum_then.logos, minimum_else.logos, "
        "lt_add_transport.logos and lt_neq_from_lt.logos"
    )
