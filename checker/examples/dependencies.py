"""Derive Q from P ∧ Q through a reusable lemma, then export the target."""
import sys
from pathlib import Path

import logos
from logos.kernel import AndElimR, AxiomRef
from logos.tactics import apply, exact

p, q = logos.vars("P Q", bool)


@logos.axiom
def A():
    return p & q


@logos.theorem
def L():
    return q


L.proof(exact(AndElimR(AxiomRef(A))))


@logos.theorem
def T():
    return q


if __name__ == "__main__":
    output = Path(sys.argv[1] if len(sys.argv) > 1 else "authored-dependencies.logos")
    logos.check(L)
    logos.check(T.proof(apply(L)))
    logos.export_proof(T, output)
    print(output)
