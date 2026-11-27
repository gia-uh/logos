"""Instructor solutions for chapters 03–05.

Run with Python and the installed Rust Logos checker on PATH.
"""

import logos
from logos import Int, Prop, exists, forall, lit


@logos.theorem
def rearrange(P: Prop, Q: Prop, R: Prop):
    return ((P & Q) & R) >> (Q & (R & P))


@rearrange.proof
def prove_rearrange(p, P, Q, R):
    triple = p.assume((P & Q) & R)
    pq = triple.left()
    rp = p.and_intro(triple.right(), pq.left())
    # The final inputs prove Q and R & P in that order.
    return p.and_intro(pq.right(), rp)


@logos.theorem
def eliminate_right(P: Prop, Q: Prop):
    return ((P | Q) & ~Q) >> P


@eliminate_right.proof
def prove_eliminate_right(p, P, Q):
    given = p.assume((P | Q) & ~Q)
    with p.cases(given.left()) as cases:
        with cases.left() as p_case:
            cases.finish(p_case)
        with cases.right() as q_case:
            falsehood = p.not_elim(given.right(), q_case)
            cases.finish(p.ex_falso(falsehood))
    return cases.result


@logos.theorem
def rearranged_dilemma(P: Prop, Q: Prop, R: Prop):
    return (((Q >> R) & (P | Q)) & (P >> R)) >> R


@rearranged_dilemma.proof
def prove_rearranged_dilemma(p, P, Q, R):
    given = p.assume(((Q >> R) & (P | Q)) & (P >> R))
    from_q_and_either = given.left()
    from_p = given.right()
    from_q = from_q_and_either.left()
    with p.cases(from_q_and_either.right()) as cases:
        with cases.left() as p_case:
            cases.finish(p.apply(from_p, p_case))
        with cases.right() as q_case:
            cases.finish(p.apply(from_q, q_case))
    return cases.result


@logos.theorem
def not_every_integer_below_one():
    return exists(Int, lambda n: ~(n < lit(1)))


@not_every_integer_below_one.proof
def prove_not_every_integer_below_one(p):
    # The law already proves the intermediate negation at 1.
    return p.witness(1, p.order("lt_irrefl", 1))


@logos.theorem
def triple_even(a: Int):
    return exists(Int, lambda i: a == 2 * i) >> exists(Int, lambda k: 3 * a == 2 * k)


@triple_even.proof
def prove_triple_even(p, a):
    i, a_eq = p.obtain(p.assume(exists(Int, lambda i: a == 2 * i)))
    k = 3 * i
    return p.witness(k, p.ring(3 * a == 2 * k, using=[a_eq]))


@logos.theorem
def double_of_even(a: Int):
    return exists(Int, lambda i: a == 2 * i) >> exists(Int, lambda k: a + a == 2 * k)


@double_of_even.proof
def prove_double_of_even(p, a):
    p.assume(exists(Int, lambda i: a == 2 * i))
    return p.witness(a, p.ring(a + a == 2 * a))


@logos.theorem
def double_is_even(a: Int):
    return exists(Int, lambda k: a + a == 2 * k)


@double_is_even.proof
def prove_double_is_even(p, a):
    return p.witness(a, p.ring(a + a == 2 * a))


@logos.theorem
def equal_offsets(a: Int, b: Int):
    return (a == b) >> forall(
        Int, lambda x: exists(Int, lambda y: (a + x == y) & (b + x == y))
    )


@equal_offsets.proof
def prove_equal_offsets(p, a, b):
    equal = p.assume(a == b)
    with p.fix("x") as fixed:
        x = fixed.variable
        y = b + x
        left = p.ring(a + x == y, using=[equal])
        fixed.finish(p.witness(y, p.and_intro(left, p.refl(y))))
    return fixed.result


if __name__ == "__main__":
    for theorem in (
        rearrange,
        eliminate_right,
        rearranged_dilemma,
        not_every_integer_below_one,
        triple_even,
        double_of_even,
        double_is_even,
        equal_offsets,
    ):
        theorem.check()
        assert theorem.certified
        print(f"{theorem.name}: {theorem.certified}")
