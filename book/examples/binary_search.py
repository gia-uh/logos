import logos
from logos.expr import Lit, Var


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
    n = logos.length(xs)

    lower_cut = logos.forall(
        int, lambda i: (Lit(0) <= i) >> ((i < low) >> (logos.nth(xs, i) < target))
    )
    upper_cut = logos.forall(
        int, lambda i: (high <= i) >> ((i < n) >> (target < logos.nth(xs, i)))
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
        | ((Lit(0) <= result)
           & (result < n)
           & (logos.nth(xs, result) == target))
    )
    return logos.program_contract(
        requires=logos.sorted(xs),
        ensures=ensures,
        invariant=invariant,
        variant=high - low,
    )


def main() -> None:
    binary_search_correct.check()
    print("binary_search_correct:", binary_search_correct.certified)
    print("obligations:", ", ".join(binary_search_correct.program.obligations))
    logos.export_proof(binary_search_correct, "binary_search.logos")
    print("certificate: binary_search.logos")


if __name__ == "__main__":
    main()
