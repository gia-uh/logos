"""Prove a contract about an ordinary Python function from its source.

Install the wheel and put the Rust checker on PATH, then from the repository
root run:

    python examples/function_contract.py
    logos check --strict advance.logos

The exported statement is

    forall mid:int, forall result:int, result = advance(mid) -> result - mid = 1

where ``advance`` is declared to the checker as the transparent function
``advance(mid) = mid + 1`` extracted from this file.
"""
import logos


def advance(mid: int) -> int:
    return mid + 1


@logos.theorem(about=advance)
def advances(mid, *, result):
    return logos.contract(ensures=(result - mid == 1))


if __name__ == "__main__":
    advances.check()
    logos.export_proof(advances, "advance.logos")
    print(advances.statement)
    print("wrote advance.logos")
