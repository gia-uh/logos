import json
import subprocess

import pytest

import logos
from logos.domains import _finite
from logos.domains.logic_puzzles import KnightsKnaves
from logos.runner import TrailingTactics


@pytest.mark.parametrize(("claim", "expected"), [
    (lambda a, b: a.is_knave(), "A is a knave."),
    (lambda a, b: a.is_knave() & b.is_knight(), "A is a knave and B is a knight."),
    (lambda a, b: ~(a.is_knave() & b.is_knave()), "A and B are not both knaves."),
    (lambda a, b: ~(a.is_knave() | b.is_knave()), "Neither A nor B is a knave."),
    (lambda a, b: ~(a.is_knight() | b.is_knight()), "Neither A nor B is a knight."),
    (lambda a, b: ~a.is_knave() & ~b.is_knave(), "Neither A nor B is a knave."),
    (lambda a, b: ~a.is_knight() & ~b.is_knight(), "Neither A nor B is a knight."),
    (lambda a, b: ~a.is_knave() & ~b.is_knight(),
     "(it is false that A is a knave) and (it is false that B is a knight)."),
    (lambda a, b: ~a.is_knave() & ~a.is_knave(),
     "(it is false that A is a knave) and (it is false that A is a knave)."),
    (lambda a, b: ~~a.is_knave() & ~~b.is_knave(),
     "(it is false that (it is false that A is a knave)) and "
     "(it is false that (it is false that B is a knave))."),
    (lambda a, b: ~(a.is_knave() & b.is_knight()),
     "It is false that (A is a knave and B is a knight)."),
    (lambda a, b: ~(a.is_knave() | a.is_knave()),
     "It is false that (A is a knave or A is a knave (or both))."),
    (lambda a, b: ~a.is_knave() | ~b.is_knave(),
     "(it is false that A is a knave) or (it is false that B is a knave) (or both)."),
    (lambda a, b: ~~a.is_knave(), "It is false that (it is false that A is a knave)."),
    (lambda a, b: (a.is_knave() >> b.is_knave()) >> (a.is_knight() | b.is_knight()),
     "If (if A is a knave, then B is a knave), then (A is a knight or B is a knight (or both))."),
    (lambda a, b: (a.is_knave() | b.is_knave()) >> (a.is_knight() >> b.is_knight()),
     "If (A is a knave or B is a knave (or both)), then (if A is a knight, then B is a knight)."),
    (lambda a, b: a.is_knave() | (a.is_knight() & b.is_knight()),
     "A is a knave or (A is a knight and B is a knight) (or both)."),
    (lambda a, b: (a.is_knave() | a.is_knight()) & b.is_knight(),
     "(A is a knave or A is a knight (or both)) and B is a knight."),
    (lambda a, b: a.is_knight() >> logos.lit(False),
     "If A is a knight, then a contradiction holds."),
])
def test_describe_preserves_claim_structure_before_proof(claim, expected):
    puzzle = KnightsKnaves()
    a, b = puzzle.entity("A"), puzzle.entity("B")
    # Even invalid recorded speech is irrelevant to rendering a valid claim.
    a.says(logos.lit(True))
    expr = claim(a, b)
    assert puzzle.describe(expr) == puzzle.describe(expr) == expected
    assert puzzle.solve_status is None


def test_describe_quotes_and_escapes_names():
    puzzle = KnightsKnaves()
    a = puzzle.entity('A or "B"\n\x1b')
    b = puzzle.entity("Éloi")
    assert puzzle.describe(~(a.is_knave() & b.is_knave())) == (
        r'"A or \"B\"\n\u001b" and "\u00c9loi" are not both knaves.'
    )
    everyone = puzzle.entity("Everyone")
    assert puzzle.describe(everyone.is_knight()) == '"Everyone" is a knight.'


def test_describe_rejects_unsupported_and_foreign_expressions():
    puzzle = KnightsKnaves()
    a = puzzle.entity("A")
    other_a = KnightsKnaves().entity("A")
    for claim, error in (
        (a.is_knight() >> other_a.is_knight(), "A_kn.*must belong to this puzzle"),
        (a.is_knight() & (a.is_knight() == a.is_knave()), "unsupported statement Eq"),
        (logos.lit(True), "unsupported statement Lit"),
        (a.is_knight() | False, "unsupported statement bool"),
    ):
        with pytest.raises(ValueError, match=error):
            puzzle.describe(claim)


@pytest.mark.parametrize(("describe", "expected"), [
    (lambda a, b: a.says(a.is_knave() & b.is_knave()), {"A": "knave", "B": "knight"}),
    # A says they differ. B says A is a knave. The second statement requires
    # different roles, so A is truthful and B is lying.
    (lambda a, b: (a.says(~(a.is_knight() >> b.is_knight()) | ~(b.is_knight() >> a.is_knight())),
                   b.says(a.is_knave())), {"A": "knight", "B": "knave"}),
    # A lies because a contradiction is always false. B's two observations
    # are both true once A lies.
    (lambda a, b: (a.says(a.is_knave() & ~a.is_knave()),
                   b.says(~(a.is_knight() | logos.lit(False))).says(a.is_knave())),
     {"A": "knave", "B": "knight"}),
])
def test_unique_assignment_and_strict_replay(tmp_path, describe, expected):
    puzzle = KnightsKnaves()
    a, b = puzzle.entity("A"), puzzle.entity("B")
    describe(a, b)
    assert puzzle.solve() == expected
    assert puzzle.solve_status == "unique"

    path = tmp_path / "assignment.logos"
    receipt = puzzle.export_proof(path)
    assert receipt.artifact == path.read_bytes()
    result = subprocess.run(
        ["logos", "check", "--json", "--strict", str(path)],
        check=True, capture_output=True, text=True,
    )
    checked = json.loads(result.stdout)
    assert checked["custom_axioms"] == []
    assert checked["artifact_sha256"] == receipt.artifact_sha256
    target = checked["statement"]
    while target["tag"] == "implies":
        target = target["right"]
    names = {symbol["id"]: symbol["name"] for symbol in checked["declarations"]}
    suffix = {"knight": "kn", "knave": "kv"}
    assert target["tag"] == "and"
    assert [names[target[side]["id"]] for side in ("left", "right")] == [
        f"{name}_{suffix[role]}" for name, role in expected.items()
    ]


def test_alternatives_and_no_model_are_distinct(tmp_path):
    puzzle = KnightsKnaves()
    a, b = puzzle.entity("A"), puzzle.entity("B")
    a.says(b.is_knight())
    assert puzzle.solve() == [
        {"A": "knight", "B": "knight"}, {"A": "knave", "B": "knave"},
    ]
    assert puzzle.solve_status == "underdetermined"
    with pytest.raises(logos.LogosProofError, match="unique assignment"):
        puzzle.export_proof(tmp_path / "ambiguous.logos")

    b.says(b.is_knave())
    assert puzzle.solve() is None
    assert puzzle.solve_status == "inconsistent"
    with pytest.raises(logos.LogosProofError, match="unique assignment"):
        puzzle.export_proof(tmp_path / "inconsistent.logos")
    assert not list(tmp_path.iterdir())


def test_timeout_discards_a_partial_search(monkeypatch, tmp_path):
    puzzle = KnightsKnaves()
    puzzle.entity("A")
    puzzle.entity("B")
    # Expire after reaching the first model and before checking the next branch.
    times = iter([0, 0, 0, 0, 1])
    monkeypatch.setattr(_finite, "monotonic", lambda: next(times))
    assert puzzle.solve(timeout=0.5) is None
    assert puzzle.solve_status == "unknown"
    with pytest.raises(logos.LogosProofError, match="unique assignment"):
        puzzle.export_proof(tmp_path / "partial.logos")
    assert not list(tmp_path.iterdir())


def test_mutation_invalidates_the_previous_proof(tmp_path):
    puzzle = KnightsKnaves()
    a = puzzle.entity("A")
    a.says(a.is_knight() | a.is_knave())
    assert puzzle.solve() == {"A": "knight"}
    puzzle.entity("B")
    assert puzzle.solve_status is None
    with pytest.raises(logos.LogosProofError, match="unique assignment"):
        puzzle.export_proof(tmp_path / "stale.logos")
    assert len(puzzle.solve()) == 2


def test_unsupported_statements_report_the_expression_or_foreign_atom():
    puzzle = KnightsKnaves()
    a = puzzle.entity("A")
    a.says(a.is_knight() == a.is_knave())
    with pytest.raises(ValueError, match="unsupported statement Eq"):
        puzzle.solve()

    other = KnightsKnaves()
    b = other.entity("B")
    b.says(a.is_knave())
    with pytest.raises(ValueError, match="A_kv.*must belong to this puzzle"):
        other.solve()


def test_guided_cases_compose_with_standard_tactics_and_auto(tmp_path):
    puzzle = KnightsKnaves()
    a, b = puzzle.entity("A"), puzzle.entity("B")
    a.says(a.is_knave() & b.is_knave())
    claim = a.is_knave() & b.is_knight()

    proof = puzzle.prove(claim, by=[
        puzzle.cases_on_role(a),
        [puzzle.use_statements(), puzzle.auto()],
        [logos.tactics.split(), [logos.tactics.assumption()], [puzzle.auto()]],
    ])
    path = tmp_path / "guided.logos"
    logos.export_proof(proof, path)
    result = subprocess.run(
        ["logos", "inspect", "--json", "--strict", str(path)],
        check=True, capture_output=True, text=True,
    )
    trace = json.loads(result.stdout)
    assert trace["custom_axioms"] == []
    assert {"or_elim", "implies_elim", "and_intro"} <= {step["rule"] for step in trace["steps"]}
    assert puzzle.solve() == {"A": "knave", "B": "knight"}
    puzzle.export_proof(tmp_path / "automatic.logos")
    automatic = json.loads((tmp_path / "automatic.logos").read_bytes())
    assert trace["statement"] == automatic["target"]


def test_guided_failure_reports_only_the_active_branch():
    puzzle = KnightsKnaves()
    a, b = puzzle.entity("A"), puzzle.entity("B")
    a.says(a.is_knave() & b.is_knave())
    with pytest.raises(logos.LogosProofError) as raised:
        puzzle.prove(a.is_knave(), by=[
            puzzle.cases_on_role(a),
            [puzzle.use_statements(), logos.tactics.assumption()],
            [logos.tactics.assumption()],
        ])
    message = str(raised.value)
    assert message == (
        "Open goal: A is a knave\n"
        "Local hypotheses:\n"
        "  role_of_A: A is a knight\n"
        "  statement_1_by_A: (A is a knave) and (B is a knave)"
    )


def test_guided_missing_tactic_reports_the_open_goal_and_context():
    puzzle = KnightsKnaves()
    a = puzzle.entity("A")
    claim = a.is_knight() >> a.is_knight()
    with pytest.raises(logos.LogosProofError) as raised:
        puzzle.prove(claim, by=[logos.tactics.intro("h")])
    assert str(raised.value) == (
        "Open goal: A is a knight\n"
        "Local hypotheses:\n"
        "  h: A is a knight"
    )


def test_guided_trailing_tactics_reports_the_runner_cause():
    puzzle = KnightsKnaves()
    a = puzzle.entity("A")
    claim = a.is_knight() >> a.is_knight()
    with pytest.raises(logos.LogosProofError) as raised:
        puzzle.prove(claim, by=[
            logos.tactics.intro("h"),
            logos.tactics.assumption(),
            logos.tactics.assumption(),
        ])
    message = str(raised.value)
    assert "Open goal" not in message
    assert "Goal was already closed, but 1 tactic remains unapplied" in message
    assert isinstance(raised.value.__cause__, TrailingTactics)


def test_guided_trailing_tactics_in_a_nested_branch_is_not_an_open_goal():
    puzzle = KnightsKnaves()
    a = puzzle.entity("A")
    claim = a.is_knight() >> a.is_knight()
    with pytest.raises(logos.LogosProofError) as raised:
        puzzle.prove(claim, by=[
            logos.tactics.intro("h"),
            [logos.tactics.assumption()],
            logos.tactics.assumption(),
        ])
    message = str(raised.value)
    assert "Open goal" not in message
    assert "Goal was already closed" in message
    assert isinstance(raised.value.__cause__, TrailingTactics)


def test_guided_auto_distinguishes_entailment_from_underdetermination():
    puzzle = KnightsKnaves()
    a, b = puzzle.entity("A"), puzzle.entity("B")
    a.says(b.is_knight())
    assert len(puzzle.solve()) == 2
    assert puzzle.solve_status == "underdetermined"

    same_role = (a.is_knight() & b.is_knight()) | (a.is_knave() & b.is_knave())
    assert puzzle.prove(same_role, by=[puzzle.auto()]).certified

    with pytest.raises(logos.LogosProofError) as raised:
        puzzle.prove(a.is_knave(), by=[
            puzzle.cases_on_role(a), logos.tactics.all_goals(puzzle.auto()),
        ])
    message = str(raised.value)
    assert "Open goal: A is a knave" in message
    assert "role_of_A: A is a knight" in message
    assert "A valid assignment leaves the goal false: A is a knight, B is a knight." in message


def test_guided_auto_reports_budget_exhaustion():
    puzzle = KnightsKnaves()
    a = puzzle.entity("A")
    a.says(a.is_knight() | a.is_knave())
    with pytest.raises(logos.LogosProofError, match="Finite search exhausted its time budget"):
        puzzle.prove(a.is_knight(), by=[puzzle.auto(timeout=0)])


def test_guided_proof_can_use_a_lemma(tmp_path):
    puzzle = KnightsKnaves()
    a = puzzle.entity("A")
    claim = a.is_knight() >> a.is_knight()
    lemma = logos.Theorem(claim, name="role_implies_itself").proof(
        logos.tactics.intro("role"), logos.tactics.assumption(),
    )
    theorem = puzzle.prove(claim, by=[logos.tactics.apply(lemma)])
    bundle = json.loads(logos.export_proof(theorem, tmp_path / "lemma.logos").artifact)
    assert [entry["id"] for entry in bundle["lemmas"]] == ["role_implies_itself"]
