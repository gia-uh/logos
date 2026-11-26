"""Prove a contract about a function that branches on one equality.

Install the wheel and put the Rust checker on PATH, then from the repository
root run:

    python examples/branch_contract.py
    logos check --strict step_at_zero.logos
    logos check --strict step_away_from_zero.logos
    logos check --strict step_at_boundary.logos

The source fragment is one ``if``/``else`` over a single ``==`` or ``!=``
comparison of integer expressions, with one ``return`` per branch. Each
theorem supplies a ``requires=`` that selects one path: the guard selects the
then branch and its negation selects the else branch. The exported statement is

    forall x:int, forall result:int, x = 0 -> result = step[then](x) -> result = 1

and the transparent function definition is the selected branch, labelled
``step[then]`` or ``step[else]`` so it is not read as the whole function.
"""
import logos


def step(x: int) -> int:
    if x == 0:
        return 1
    else:
        return x + 1


@logos.theorem(about=step)
def step_at_zero(x, *, result):
    return logos.contract(requires=(x == 0), ensures=(result == 1))


@logos.theorem(about=step)
def step_away_from_zero(x, *, result):
    return logos.contract(requires=(x != 0), ensures=(result == x + 1))


@logos.theorem(about=step)
def step_at_boundary(x, *, result):
    # Both branches return 1 at x = 0. This claim is written in the else
    # branch's formula; the requires equality x = 0 supplies the boundary.
    return logos.contract(requires=(x == 0), ensures=(result == x + 1))


if __name__ == "__main__":
    for theorem in (step_at_zero, step_away_from_zero, step_at_boundary):
        theorem.check()
        logos.export_proof(theorem, f"{theorem.name}.logos")
        print(theorem.statement)
    print("wrote step_at_zero.logos, step_away_from_zero.logos and step_at_boundary.logos")
