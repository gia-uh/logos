"""Export the conditional proof for A's statement, 'We are both knaves.'"""
import argparse
from pathlib import Path

import logos
from logos.domains.logic_puzzles import KnightsKnaves
from logos.kernel import (
    AndElimL, AndIntro, Block, CaseAnalysis, ExFalso, HypRef, ImpliesElim,
    ImpliesIntro, NotElim, NotIntro, StepRef,
)
from logos.tactics import exact, intro


def puzzle():
    domain = KnightsKnaves()
    a = domain.entity("A")
    b = domain.entity("B")
    a_knave = a.is_knave()
    b_knave = b.is_knave()
    b_knight = b.is_knight()
    a.says(a_knave & b_knave)

    theorem = domain.theorem(a_knave & b_knight, name="knights_knaves")

    # In the knight case A speaks truly, which implies A is also a knave.
    a_role = HypRef("a_role")
    knight_claim = ImpliesElim(HypRef("a_tells_truth"), a_role)
    knight_not_knave = ImpliesElim(HypRef("a_knight_excludes_knave"), a_role)
    a_is_knave = CaseAnalysis(
        HypRef("a_has_role"), "a_role",
        ExFalso(NotElim(knight_not_knave, AndElimL(knight_claim)), a_knave),
        a_role,
    )

    # A is a knave, so the claim is false. If B were a knave, it would be true.
    claim_is_false = ImpliesElim(HypRef("a_lies"), StepRef(0))
    both_knaves = AndIntro(StepRef(0), HypRef("suppose_b_knave"))
    b_is_not_knave = NotIntro(ImpliesIntro(
        b_knave, "suppose_b_knave", NotElim(claim_is_false, both_knaves),
    ))

    # B has a role. The knave case contradicts the negation just proved.
    b_role = HypRef("b_role")
    b_is_knight = CaseAnalysis(
        HypRef("b_has_role"), "b_role", b_role,
        ExFalso(NotElim(StepRef(1), b_role), b_knight),
    )

    return theorem.proof(
        intro(
            "a_has_role", "a_knight_excludes_knave", "a_knave_excludes_knight",
            "b_has_role", "b_knight_excludes_knave", "b_knave_excludes_knight",
            "a_tells_truth", "a_lies",
        ),
        exact(Block((a_is_knave, b_is_not_knave, b_is_knight,
                     AndIntro(StepRef(0), StepRef(2))), 3)),
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    theorem = logos.check(puzzle())
    logos.export_proof(theorem, args.output)
    print(args.output)
