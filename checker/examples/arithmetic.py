"""Author integer identities with the installed checker, then export their proofs."""
import sys
from pathlib import Path

import logos
from logos import tactics as t


@logos.theorem
def reflexivity(x: int):
    return x == x


@logos.theorem
def addition_commutes(x: int, y: int):
    return x + y == y + x


@logos.theorem
def binomial_square(x: int, y: int):
    return (x + y)**2 == x**2 + 2*x*y + y**2


@logos.theorem
def signed_square(x: int):
    return (x - 1)**2 == x**2 - 2*x + 1


@logos.theorem
def additive_inverse(x: int):
    return x + (-x) == 0


@logos.theorem
def zero_power(x: int):
    return x**0 == 1


def main(output: Path):
    output.mkdir(parents=True, exist_ok=True)
    for theorem, variables, tactic in [
        (reflexivity, ("x",), t.refl()),
        (addition_commutes, ("x", "y"), t.ring()),
        (binomial_square, ("x", "y"), t.ring()),
        (signed_square, ("x",), t.ring()),
        (additive_inverse, ("x",), t.ring()),
        (zero_power, ("x",), t.ring()),
    ]:
        logos.check(theorem.proof(t.intro(*variables), tactic))
        path = output / f"{theorem.name}.logos"
        logos.export_proof(theorem, path)
        print(f"Exported {path}")


if __name__ == "__main__":
    main(Path(sys.argv[1]) if len(sys.argv) > 1 else Path("."))
