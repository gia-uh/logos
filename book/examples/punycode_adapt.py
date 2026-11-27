# Body of encodings.punycode.adapt from CPython 3.12.3, Lib/encodings/punycode.py.
# Only the type annotations are added; the executable statements are unchanged.
def adapt(delta: int, first: int, numchars: int) -> int:
    if first:
        delta //= 700
    else:
        delta //= 2
    delta += delta // numchars
    divisions = 0
    while delta > 455:
        delta = delta // 35
        divisions += 36
    bias = divisions + (36 * delta // (delta + 38))
    return bias
