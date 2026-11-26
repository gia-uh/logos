import json
import subprocess

import pytest

import logos
from logos.domains import _finite
from logos.domains.logic_puzzles import KnightsKnaves


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
