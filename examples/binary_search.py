"""Total correctness of an executable binary search over a sorted sequence.

The contract uses half-open bounds ``[low, high)``. The returned value is any
valid occurrence, or ``-1`` exactly when the target is absent. Duplicates and
the empty sequence are covered by the invariant, not by tests.

Install the wheel and the Rust checker, then from the repository root run:

    python examples/binary_search.py
    logos check --strict binary_search.logos

The source is bound to the imported code object. The Rust checker recomputes
the loop verification conditions and checks every proof term; this script only
proposes them.
"""
import logos
from logos.expr import ForallNode, Lit, Var


def binary_search(xs: list[int], target: int) -> int:
    low = 0
    high = len(xs)
    answer = -1
    while low < high:
        mid = (low + high) // 2
        if xs[mid] == target:
            answer = mid
            low = high
        elif xs[mid] < target:
            low = mid + 1
        else:
            high = mid
    return answer


@logos.theorem(about=binary_search)
def binary_search_correct(xs, target, *, result):
    low = Var("low", int)
    high = Var("high", int)
    answer = Var("answer", int)
    i = Var("i", int)
    n = logos.length(xs)
    lower_cut = ForallNode(
        i,
        (Lit(0) <= i) >> ((i < low) >> (logos.nth(xs, i) < target)),
    )
    upper_cut = ForallNode(
        i,
        (high <= i) >> ((i < n) >> (target < logos.nth(xs, i))),
    )
    found = (
        (Lit(0) <= answer)
        & (answer < n)
        & (logos.nth(xs, answer) == target)
        & ~(answer == -1)
    )
    searching = (answer == -1) & lower_cut & upper_cut
    invariant = (
        logos.sorted(xs)
        & (Lit(0) <= low)
        & (low <= high)
        & (high <= n)
        & (found | searching)
    )
    ensures = (
        ((result == -1) & logos.absent(xs, target))
        | ((Lit(0) <= result) & (result < n) & (logos.nth(xs, result) == target))
    )
    return logos.program_contract(
        requires=logos.sorted(xs),
        ensures=ensures,
        invariant=invariant,
        variant=high - low,
    )


if __name__ == "__main__":
    binary_search_correct.check()
    logos.export_proof(binary_search_correct, "binary_search.logos")
    print(binary_search_correct.statement)
    print("wrote binary_search.logos")
