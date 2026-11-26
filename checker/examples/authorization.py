"""Export a proof of (Authenticated ∧ Authorized) → Authorized."""
import sys
from pathlib import Path

import logos
from logos.kernel import AndElimR, HypRef

authenticated = logos.var("Authenticated", bool)
authorized = logos.var("Authorized", bool)


@logos.theorem
def authorization():
    return (authenticated & authorized) >> authorized


def project_authorized(goal):
    return AndElimR(HypRef("h"))


if __name__ == "__main__":
    output = Path(sys.argv[1] if len(sys.argv) > 1 else "authored.logos")
    authorization.proof(logos.tactics.intro("h"), project_authorized)
    logos.check(authorization)
    logos.export_proof(authorization, output)
    print(output)
