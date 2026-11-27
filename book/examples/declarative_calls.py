import logos


@logos.function
def first(xs: list[int]) -> int:
    """Return the first element of a nonempty sequence."""
    return xs[0]


@first.requires
def nonempty(xs):
    return 0 < logos.length(xs)


@first.ensures
def returns_first(xs, *, result):
    return result == logos.nth(xs, 0)


@logos.function
def first_or_zero(xs: list[int]) -> int:
    """Return the first element, or zero when the sequence is empty."""
    if len(xs) == 0:
        return 0
    else:
        return first(xs)


@first_or_zero.ensures
def zero_or_first(xs, *, result):
    return (result == 0) | (result == logos.nth(xs, 0))


@first_or_zero.ensures
def exact_first_or_zero(xs, *, result):
    return ((logos.length(xs) == 0) >> (result == 0)) & (
        (0 < logos.length(xs)) >> (result == logos.nth(xs, 0))
    )
