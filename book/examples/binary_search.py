import logos


@logos.function
def binary_search(xs: list[int], target: int) -> int:
    """Return an index holding target in a sorted sequence, or -1 if absent."""
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


@binary_search.ensures
def finds_or_absent(xs, target, *, result):
    n = logos.length(xs)
    return ((result == -1) & logos.absent(xs, target)) | (
        (0 <= result) & (result < n) & (logos.nth(xs, result) == target)
    )


@binary_search.requires
def ordered(xs):
    return logos.sorted(xs)


@binary_search.invariant
def below_cut(xs, target, *, low, answer):
    return (answer == -1) >> logos.forall(
        int, lambda i: (0 <= i) >> ((i < low) >> (logos.nth(xs, i) < target))
    )


@binary_search.invariant
def above_cut(xs, target, *, high, answer):
    n = logos.length(xs)
    return (answer == -1) >> logos.forall(
        int, lambda i: (high <= i) >> ((i < n) >> (target < logos.nth(xs, i)))
    )


@binary_search.invariant
def keeps_order(xs):
    return logos.sorted(xs)


@binary_search.invariant
def bounds(xs, *, low, high):
    return (0 <= low) & (low <= high) & (high <= logos.length(xs))


@binary_search.invariant
def answer_or_searching(xs, target, *, low, high, answer):
    n = logos.length(xs)
    lower = logos.forall(
        int, lambda i: (0 <= i) >> ((i < low) >> (logos.nth(xs, i) < target))
    )
    upper = logos.forall(
        int, lambda i: (high <= i) >> ((i < n) >> (target < logos.nth(xs, i)))
    )
    found = (
        (0 <= answer) & (answer < n)
        & (logos.nth(xs, answer) == target) & ~(answer == -1)
    )
    searching = (answer == -1) & lower & upper
    return found | searching


@binary_search.decreases
def remaining(*, low, high):
    return high - low
