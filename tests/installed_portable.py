"""Exercise portable proofs with an installed binary and wheel.

Authoring is a scripted smoke: the test writes its own caller code. An
independent recipient trial is separate and is not claimed here.
"""
import argparse
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile


FIXTURES = Path(__file__).resolve().parents[1] / "checker/tests/fixtures/portable"
EXPECTED = "(Authenticated ∧ Authorized) → Authorized"

COLD_AUTHOR = """\
import logos
from logos.expr import And
from logos.kernel import AndElimR, HypRef

authenticated = logos.var("Authenticated", bool)
authorized = logos.var("Authorized", bool)

@logos.theorem
def authorization():
    return (authenticated & authorized) >> authorized

def right_permission(goal):
    if not isinstance(goal.context["permission"], And):
        raise ValueError("expected a conjunction under permission")
    return AndElimR(HypRef("permission"))

logos.check(authorization.proof(logos.tactics.intro("permission"), right_permission))
logos.export_proof(authorization, "cold.logos")
"""


def run(argv, cwd, *, env=None, code=0, show_output=True):
    print(f"$ {shlex.join(str(arg) for arg in argv)}", flush=True)
    result = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True)
    if show_output:
        print(result.stdout, end="")
    print(result.stderr, end="")
    print(f"exit {result.returncode}", flush=True)
    assert result.returncode == code
    return result


def replay(recipient, *args, offline, code=0, show_output=True):
    if not offline:
        return run(["./logos", *args], recipient, env={"PATH": ""}, code=code, show_output=show_output)

    # Use a new network namespace and an empty filesystem with only the
    # copied inputs and the binary's system loader and libraries mounted.
    command = [
        "bwrap", "--unshare-net", "--die-with-parent", "--clearenv",
        "--ro-bind", recipient / "logos", "/logos",
    ]
    artifact = recipient / args[-1]
    command.extend(["--ro-bind", artifact, f"/{artifact.name}"])
    runtime = subprocess.run(["ldd", recipient / "logos"], capture_output=True, text=True, check=True)
    for line in runtime.stdout.splitlines():
        library = next((word for word in line.split() if word.startswith("/")), None)
        if library:
            command.extend(["--ro-bind", library, library])
    return run([*command, "--chdir", "/", "--", "/logos", *args], recipient, code=code, show_output=show_output)


def arithmetic(cold, recipient, evidence, help_text, env, offline):
    heading = "To replay and author integer identities:\n"
    commands = help_text.split(heading)[1].split("\n\n")[0].splitlines()
    for line in commands:
        argv = shlex.split(line)
        run(argv, cold, env=env, show_output="--json" not in argv)

    (cold / "wrong_refl.py").write_text("""\
import logos
from logos.kernel import Refl

@logos.theorem
def same_labels_are_distinct(x: int, y: int):
    return x + y == y + x

try:
    logos.check(same_labels_are_distinct.proof(
        logos.tactics.intro("x", "x"), lambda goal: Refl(goal.statement.left)
    ))
except logos.LogosProofError as error:
    assert "proof conclusion mismatch" in str(error)
    print(error)
else:
    raise AssertionError("Python accepted the bad proof")
""")
    run(["python", "wrong_refl.py"], cold, env=env)
    (cold / "wrong_refl.py").unlink()
    (cold / "arithmetic.py").unlink()

    for path in (cold / "proofs").glob("*.logos"):
        shutil.move(path, recipient / path.name)
    shutil.move(cold / "arithmetic.logos", recipient / "arithmetic.logos")

    valid = [
        "arithmetic", "reflexivity", "addition_commutes", "binomial_square",
        "signed_square", "additive_inverse", "zero_power",
    ]
    trace = {}
    for name in valid:
        filename = f"{name}.logos"
        check = replay(recipient, "check", "--strict", filename, offline=offline)
        assert "Verified with 0 custom axioms" in check.stdout
        inspected = replay(recipient, "inspect", "--json", "--strict", filename,
                           offline=offline, show_output=False)
        data = json.loads(inspected.stdout)
        assert data["status"] == "verified" and data["custom_axioms"] == []
        checked_steps = set()
        scope_ids = {scope["id"] for scope in data["contexts"]}
        for step in data["steps"]:
            assert set(step["premises"]) <= checked_steps
            assert step["context_id"] in scope_ids
            assert step["explanation"] and step["conclusion_sort"] == "prop"
            checked_steps.add(step["id"])
        claim = data["claim"]
        assert claim["proof_step"] in checked_steps
        assert claim["statement_field"] == "statement"
        shutil.copy2(recipient / filename, evidence / filename)
        (evidence / f"{name}.inspect.json").write_text(inspected.stdout)
        trace[name] = data
        print(f"{filename}: {(recipient / filename).stat().st_size} proof bytes, "
              f"{len(checked_steps)} checked steps, {len(inspected.stdout.encode())} trace bytes")

    comm = trace["addition_commutes"]
    [law] = [step for step in comm["steps"] if step["rule"] == "core_law"]
    assert law["reference_id"] == law["law"]["id"] == "add_comm"
    substitution = law["law"]["substitution"]
    assert [item["formal"] for item in substitution] == ["a", "b"]
    assert [item["actual"]["index"] for item in substitution] == [0, 1]
    scope = next(scope for scope in comm["contexts"] if scope["id"] == law["context_id"])
    assert [(v["name"], v["sort"]) for v in scope["variables"]] == [("x", "int"), ("y", "int")]
    assert law["conclusion_text"] == "(y + x) = (x + y)"
    square_rules = {step["rule"] for step in trace["binomial_square"]["steps"]}
    assert {"core_law", "congr", "trans", "step_ref"} <= square_rules
    assert any(step.get("reference_id") == "distrib" for step in trace["binomial_square"]["steps"])
    assert len(trace["binomial_square"]["steps"]) < 250
    assert (recipient / "binomial_square.logos").stat().st_size < 20_000
    assert any(step.get("conclusion_conversion") for step in trace["zero_power"]["steps"])

    def mutate(source, filename, change):
        data = json.loads((recipient / f"{source}.logos").read_text())
        change(data)
        (recipient / filename).write_text(json.dumps(data) + "\n")

    def wrong_reflexivity(data):
        data["proof"]["body"]["body"] = {
            "tag": "refl", "term": data["target"]["body"]["body"]["left"],
        }

    def wrong_scope(data):
        data["proof"]["body"]["term"]["index"] = 1

    def wrong_sort(data):
        data["proof"]["sort"] = "prop"

    def wrong_constant(data):
        data["target"]["body"]["right"]["right"]["value"] = "2"

    def equal_distinct_variables(data):
        data["target"]["body"]["body"] = {
            "tag": "eq", "left": {"tag": "bound", "index": 1},
            "right": {"tag": "bound", "index": 0},
        }
        wrong_reflexivity(data)

    for source, filename, change, reason in [
        ("addition_commutes", "wrong-reflexivity.logos", wrong_reflexivity, "proof conclusion mismatch"),
        ("addition_commutes", "wrong-variables.logos", equal_distinct_variables, "proof conclusion mismatch"),
        ("reflexivity", "wrong-scope.logos", wrong_scope, "out-of-scope bound variable"),
        ("reflexivity", "wrong-sort.logos", wrong_sort, "proof conclusion mismatch"),
        ("signed_square", "wrong-constant.logos", wrong_constant, "proof conclusion mismatch"),
    ]:
        mutate(source, filename, change)
        for operation in ("check", "inspect"):
            for flags in ([], ["--strict"]):
                invalid = replay(recipient, operation, "--json", *flags, filename, offline=offline, code=1)
                assert not invalid.stdout
                error = json.loads(invalid.stderr)
                assert error["status"] == "error" and reason in error["error"]
        shutil.copy2(recipient / filename, evidence / filename)


def existentials(cold, recipient, evidence, env, offline):
    author = cold / "successor.py"
    author.write_text("""\
import logos
import logos.tactics as t
from logos.kernel import Refl


@logos.theorem
def integer_successor(x: int):
    return logos.exists(int, lambda y: y == x + 1)


def choose_successor(goal):
    return t.witness(goal.context["x"] + 1)(goal)


logos.check(integer_successor.proof(t.intro("x"), choose_successor, t.refl()))
logos.export_proof(integer_successor, "successor.logos")


def choose_two_more(goal):
    return t.witness(goal.context["x"] + 2)(goal)


def same_evidence(goal):
    return Refl(goal.context["x"] + 1)


try:
    logos.check(integer_successor.proof(t.intro("x"), choose_two_more, same_evidence))
except logos.LogosProofError as error:
    assert "proof does not establish the instantiated existential predicate" in str(error)
    assert not integer_successor.certified
    print(error)
else:
    raise AssertionError("Python accepted the changed witness")
""")
    run(["python", "-I", author.name], cold, env=env)
    author.unlink()
    source = recipient / "successor.logos"
    shutil.move(cold / source.name, source)

    checked = replay(recipient, "check", "--strict", source.name, offline=offline)
    assert "∀x:int, ∃y:int, y = (x + 1)" in checked.stdout
    assert "Verified with 0 custom axioms" in checked.stdout
    inspected = replay(recipient, "inspect", "--json", "--strict", source.name, offline=offline)
    data = json.loads(inspected.stdout)
    [step] = [step for step in data["steps"] if step["rule"] == "exists_intro"]
    [witness] = step["substitutions"]
    assert step["binder_sort"] == "int"
    assert witness["left"] == {"tag": "bound", "index": 0}
    assert witness["right"] == {"tag": "int", "value": "1"}
    [premise] = [item for item in data["steps"] if item["id"] in step["premises"]]
    assert premise["context_id"] == step["context_id"]
    assert premise["conclusion_text"] == "(x + 1) = (x + 1)"
    md = replay(recipient, "inspect", "--markdown", "--strict", source.name, offline=offline)
    assert r"\exists y \in \mathbb{Z}" in md.stdout
    assert "The checked premise establishes the predicate with this witness. From (" in md.stdout
    assert "The witness term is $`x + 1`$." in md.stdout
    shutil.copy2(source, evidence / source.name)
    (evidence / "successor.inspect.json").write_text(inspected.stdout)
    (evidence / "successor.md").write_text(md.stdout)

    for name, witness, diagnostic in [
        (
            "different",
            {**witness, "right": {"tag": "int", "value": "2"}},
            "proof does not establish the instantiated existential predicate",
        ),
        ("wrong-sort", {"tag": "false"}, "existential witness has sort prop, expected int"),
        ("escaped", {"tag": "bound", "index": 1}, "out-of-scope bound variable 1"),
    ]:
        bundle = json.loads(source.read_text())
        bundle["proof"]["body"]["witness"] = witness
        path = recipient / f"successor-{name}.logos"
        path.write_text(json.dumps(bundle) + "\n")
        for operation in ("check", "inspect"):
            invalid = replay(recipient, operation, "--json", "--strict", path.name, offline=offline, code=1)
            assert not invalid.stdout
            assert diagnostic in json.loads(invalid.stderr)["error"]
        shutil.copy2(path, evidence / path.name)


def markdown(recipient, evidence, offline):
    for name in ("addition_commutes", "binomial_square", "signed_square", "authorization"):
        reply = replay(recipient, "inspect", "--markdown", "--strict", f"{name}.logos",
                       offline=offline, show_output=False)
        assert reply.stdout.startswith("# Checked proof\n")
        assert "Uses zero custom axioms." in reply.stdout
        assert "\n$$\n" in reply.stdout
        assert "## Conclusion" in reply.stdout
        (evidence / f"{name}.md").write_text(reply.stdout)

    square = (evidence / "binomial_square.md").read_text()
    target_math = square.split("## Theorem\n\n$$\n", 1)[1].split("\n$$", 1)[0]
    assert r"\left(x + y\right)^{2}" in target_math
    assert square.count("**Premise conversion.**") >= 2
    assert r"\text{First middle expression}" in square
    assert r"\text{Second middle expression}" in square
    assert r"\text{Common normal form}" in square
    declared = r"\text{Declared statement}\quad & "
    assert declared + target_math in square
    assert target_math in square.split("## Conclusion", 1)[1]
    assert r"a^{n+1} = a^n \cdot a" in square
    assert "Distribute an integer factor across the two summands." in square
    assert "be arbitrary." in square
    assert "Combine the equalities by transitivity." in square
    assert "the same normal form under the core conversion rules" in square
    for implementation_detail in ("proof.body", ".steps[", "lemma[", "step_ref", "Artifact SHA-256", "context_id"):
        assert implementation_detail not in square
    comm = (evidence / "addition_commutes.md").read_text()
    assert r"a \mapsto y, b \mapsto x" in comm
    assert "earlier checked step in this block" not in comm

    valid = replay(recipient, "inspect", "--markdown", "dependencies.logos",
                   offline=offline, show_output=False)
    assert "Assumption 1" in valid.stdout and "earlier checked lemma" in valid.stdout
    (evidence / "dependencies.md").write_text(valid.stdout)
    denied = replay(recipient, "inspect", "--markdown", "--strict", "dependencies.logos",
                    offline=offline, code=3, show_output=False)
    assert "Strict policy denied" in denied.stdout and "Assumption 1" in denied.stdout
    (evidence / "strict-denied.md").write_text(denied.stdout)

    for filename in ("wrong-reflexivity.logos", "wrong-constant.logos"):
        rejected = replay(recipient, "inspect", "--markdown", "--strict", filename,
                          offline=offline, code=1)
        assert not rejected.stdout and "proof conclusion mismatch" in rejected.stderr
    ambiguous = replay(recipient, "inspect", "--markdown", "--json", "arithmetic.logos",
                       offline=offline, code=2)
    assert not ambiguous.stdout and "mutually exclusive" in ambiguous.stderr


def knights_knaves(python, cold, recipient, evidence, env, offline):
    example = FIXTURES.parents[2] / "examples/knights_knaves.py"
    source = cold / example.name
    shutil.copy2(example, source)
    filename = "knights_knaves.logos"
    run([python, "-I", source.name, filename], cold, env=env)
    source.unlink()
    shutil.move(cold / filename, recipient / filename)

    strict = replay(recipient, "check", "--strict", filename, offline=offline)
    assert "Verified with 0 custom axioms" in strict.stdout
    inspected = replay(
        recipient, "inspect", "--json", "--strict", filename, offline=offline, show_output=False
    )
    trace = json.loads(inspected.stdout)
    assert trace["status"] == "verified" and trace["custom_axioms"] == []
    steps = {step["id"]: step for step in trace["steps"]}
    contexts = {
        scope["id"]: {hyp["id"] for hyp in scope["hypotheses"]}
        for scope in trace["contexts"]
    }
    analyses = [step for step in steps.values() if step["rule"] == "or_elim"]
    assert len(analyses) == 2
    for step in analyses:
        left, right = step["discharged_cases"]
        _, left_assumption, left_result, right_assumption, right_result = step["premises"]
        assert (left, right) == (left_assumption, right_assumption)
        for own, other, result in [(left, right, left_result), (right, left, right_result)]:
            active = contexts[steps[result]["context_id"]]
            assert own in active and other not in active
        assert {left, right}.isdisjoint(contexts[step["context_id"]])
    assert contexts[steps[trace["claim"]["proof_step"]]["context_id"]] == set()
    assert {"not_intro", "not_elim", "ex_falso"} <= {step["rule"] for step in steps.values()}
    assert all(
        step["conclusion"] == {"tag": "false"}
        for step in steps.values() if step["rule"] == "not_elim"
    )

    # Independently evaluate the exported premises under a concrete assignment.
    # Checking each antecedent rules out vacuous truth of the implication chain.
    assignment = {"A_kn": False, "A_kv": True, "B_kn": True, "B_kv": False}
    assert {symbol["name"] for symbol in trace["declarations"]} == assignment.keys()
    values = {symbol["id"]: assignment[symbol["name"]] for symbol in trace["declarations"]}

    def evaluate(expr):
        match expr:
            case {"tag": "symbol", "id": id_}:
                return values[id_]
            case {"tag": "not", "operand": operand}:
                return not evaluate(operand)
            case {"tag": "and", "left": left, "right": right}:
                return evaluate(left) and evaluate(right)
            case {"tag": "or", "left": left, "right": right}:
                return evaluate(left) or evaluate(right)
            case {"tag": "implies", "left": left, "right": right}:
                return not evaluate(left) or evaluate(right)
        raise AssertionError(f"Unexpected puzzle expression: {expr!r}")

    conclusion = trace["statement"]
    premises = []
    while conclusion["tag"] == "implies":
        premises.append(evaluate(conclusion["left"]))
        conclusion = conclusion["right"]
    assert len(premises) == 8 and all(premises)
    names = {symbol["id"]: symbol["name"] for symbol in trace["declarations"]}
    assert conclusion["tag"] == "and"
    assert [names[conclusion[side]["id"]] for side in ("left", "right")] == ["A_kv", "B_kn"]
    assert evaluate(conclusion)
    print(f"A knave, B knight satisfies all {len(premises)} model premises and the conclusion")

    rendered = replay(
        recipient, "inspect", "--markdown", "--strict", filename, offline=offline, show_output=False
    ).stdout
    assert rendered.count("Discharge both case assumptions.") == 2
    assert "Assume the left disjunct" in rendered and "Assume the right disjunct" in rendered
    assert r"\neg" in rendered and r"\bot" in rendered
    assert "Uses zero custom axioms" in rendered
    assert all(id_ not in rendered for id_ in steps if id_.startswith("proof."))
    (evidence / "knights_knaves.md").write_text(rendered)
    (evidence / "knights_knaves.json").write_text(inspected.stdout)
    (evidence / "knights_knaves_model.json").write_text(json.dumps({
        "assignment": assignment, "premise_values": premises, "conclusion": evaluate(conclusion),
    }, indent=2) + "\n")
    shutil.copy2(recipient / filename, evidence / filename)


def solve_knights_knaves(cold, recipient, evidence, help_text, env, offline):
    heading = "To solve a Knights and Knaves puzzle from its inhabitants and utterances:\n"
    commands = help_text.split(heading)[1].split("\n\n")[0].splitlines()
    for line in commands:
        result = run(shlex.split(line), cold, env=env)
        if line.strip().startswith("python "):
            assert result.stdout.strip() == "{'A': 'knave', 'B': 'knight'}"
    (cold / "solve_knights_knaves.py").unlink()
    filename = "puzzle.logos"
    shutil.move(cold / filename, recipient / filename)
    check = replay(recipient, "check", "--json", "--strict", filename, offline=offline)
    solved = json.loads(check.stdout)
    manual = json.loads((evidence / "knights_knaves.json").read_text())
    assert solved["statement"] == manual["statement"]
    assert solved["custom_axioms"] == []

    bundle = json.loads((recipient / filename).read_text())
    head = bundle["target"]
    while head["right"]["tag"] == "implies":
        head = head["right"]
    head["right"] = head["right"]["left"]
    wrong = "wrong-solved-puzzle.logos"
    (recipient / wrong).write_text(json.dumps(bundle))
    rejection = replay(recipient, "check", "--json", "--strict", wrong, offline=offline, code=1)
    assert "proof conclusion mismatch" in json.loads(rejection.stderr)["error"]
    for artifact in (filename, wrong):
        shutil.copy2(recipient / artifact, evidence / artifact)

    heading = "To describe A's utterance and a proposed conclusion before proving:\n"
    [line] = help_text.split(heading)[1].split("\n\n")[0].splitlines()
    preview = [
        "A says, “A is a knave and B is a knave.”",
        "Proposed conclusion — A is a knave.",
    ]
    interpreter, script = shlex.split(line)
    preview_dir = cold / "preview"
    preview_dir.mkdir()
    # Use the installed Python directly with no checker on PATH.
    result = run([shutil.which(interpreter, path=env["PATH"]), "-I", cold / script],
                 preview_dir, env={"PATH": ""})
    assert result.stdout.splitlines() == preview
    assert not list(preview_dir.iterdir())

    heading = "To guide a proof of a specific claim in the same puzzle:\n"
    for line in help_text.split(heading)[1].split("\n\n")[0].splitlines():
        result = run(shlex.split(line), cold, env=env)
        if line.strip().startswith("python "):
            assert result.stdout.splitlines() == [
                *preview,
                "Checked conditional proof from the role and utterance premises.",
                "guided.logos",
            ]
    (cold / "guide_knights_knaves.py").unlink()
    shutil.move(cold / "guided.logos", recipient / "guided.logos")
    inspected = replay(
        recipient, "inspect", "--json", "--strict", "guided.logos",
        offline=offline, show_output=False,
    )
    guided = json.loads(inspected.stdout)
    assert guided["custom_axioms"] == []
    assert {"or_elim", "implies_elim"} <= {step["rule"] for step in guided["steps"]}
    expected = solved["statement"]
    actual = guided["statement"]
    while expected["tag"] == "implies":
        assert expected["left"] == actual["left"]
        expected, actual = expected["right"], actual["right"]
    assert actual == expected["left"]
    shutil.copy2(recipient / "guided.logos", evidence / "guided.logos")


ORDER_APP = """\
def minimum(x: int, y: int) -> int:
    if x < y:
        return x
    else:
        return y
"""

ORDER_TEST = """\
import logos
from logos import tactics as t

import app


@logos.theorem(about=app.minimum)
def minimum_then(x, y, *, result):
    return logos.contract(requires=(x < y), ensures=(result == x))


@logos.theorem(about=app.minimum)
def minimum_else(x, y, *, result):
    return logos.contract(requires=~(x < y), ensures=(result == y))


@logos.theorem
def lt_add_transport(x: int, y: int, c: int):
    return (x < y) >> ((x + c) < (y + c))


@logos.theorem
def lt_neq_from_lt(x: int, y: int):
    return (x < y) >> ~(x == y)


def test_order():
    assert app.minimum(3, 3) == 3
    minimum_then.check()
    minimum_else.check()
    logos.check(lt_add_transport.proof(t.intro("x", "y", "c", "h"), t.order("lt_add")))
    logos.check(lt_neq_from_lt.proof(t.intro("x", "y", "h"), t.order("lt_neq")))
    for theorem in (minimum_then, minimum_else, lt_add_transport, lt_neq_from_lt):
        assert theorem.certified
        logos.export_proof(theorem, theorem.name + ".logos")
"""

ORDER_STALE = """\
import pathlib
import types

import app
import logos


@logos.theorem(about=app.minimum)
def minimum_then(x, y, *, result):
    return logos.contract(requires=(x < y), ensures=(result == x))


@logos.theorem(about=app.minimum)
def minimum_else(x, y, *, result):
    return logos.contract(requires=~(x < y), ensures=(result == y))


minimum_then.check()
minimum_else.check()
path = pathlib.Path(app.__file__)
source = path.read_text()
original = app.minimum.__code__


def install(text):
    path.write_text(text)
    compiled = compile(text, str(path), "exec")
    app.minimum.__code__ = next(
        value for value in compiled.co_consts
        if isinstance(value, types.CodeType) and value.co_name == "minimum"
    )


for changed in (source.replace("x < y", "y < x"), source.replace("x < y", "x == y"),
                source.replace("return x", "return x + 1", 1),
                source.replace("return y", "return x")):
    install(changed)
    for theorem in (minimum_then, minimum_else):
        assert not theorem.certified
        try:
            theorem.check()
        except logos.LogosContractError:
            pass
        else:
            raise AssertionError("a stale order branch was accepted")
    path.write_text(source)
    app.minimum.__code__ = original

minimum_then.check()
minimum_else.check()
assert minimum_then.certified and minimum_else.certified
print("order guard and branch mutations invalidated both paths and restored")
"""

CONTRACT_APP = """\
def advance(mid: int) -> int:
    return mid + 1
"""

CONTRACT_MUTATED = """\
def advance(mid: int) -> int:
    return mid
"""

CONTRACT_PAIR = """\
def first(x: int, y: int) -> int:
    return x
"""

CONTRACT_BRANCH_APP = """\
def step(x: int) -> int:
    if x == 0:
        return 1
    else:
        return x + 1
"""

CONTRACT_BRANCH_TEST = """\
import logos
import app


@logos.theorem(about=app.step)
def step_at_zero(x, *, result):
    return logos.contract(requires=(x == 0), ensures=(result == 1))


@logos.theorem(about=app.step)
def step_away_from_zero(x, *, result):
    return logos.contract(requires=(x != 0), ensures=(result == x + 1))


@logos.theorem(about=app.step)
def step_at_boundary(x, *, result):
    return logos.contract(requires=(x == 0), ensures=(result == x + 1))


def test_branches():
    for theorem in (step_at_zero, step_away_from_zero, step_at_boundary):
        theorem.check()
        assert theorem.certified
        logos.export_proof(theorem, theorem.name + ".logos")
"""

CONTRACT_BRANCH_STALE = """\
import pathlib
import types

import app
import logos


@logos.theorem(about=app.step)
def at_zero(x, *, result):
    return logos.contract(requires=(x == 0), ensures=(result == 1))


@logos.theorem(about=app.step)
def away(x, *, result):
    return logos.contract(requires=(x != 0), ensures=(result == x + 1))


at_zero.check()
away.check()
path = pathlib.Path(app.__file__)
source = path.read_text()
original = app.step.__code__


def install(text):
    path.write_text(text)
    compiled = compile(text, str(path), "exec")
    app.step.__code__ = next(
        value for value in compiled.co_consts
        if isinstance(value, types.CodeType) and value.co_name == "step"
    )


def refused(label, needle):
    for action in (at_zero.check, away.check,
                   lambda: logos.export_proof(at_zero, "stale.logos")):
        try:
            action()
        except logos.LogosProofError as error:
            assert needle in str(error), (needle, str(error))
        else:
            raise AssertionError(f"{label} accepted stale evidence")
    assert not pathlib.Path("stale.logos").exists()


for label, text, needle in (
    ("guard", source.replace("x == 0", "x == 1"), "guard changed"),
    ("then branch", source.replace("return 1", "return 2"), "then branch changed"),
    ("else branch", source.replace("return x + 1", "return x"), "else branch changed"),
):
    install(text)
    assert not at_zero.certified and not away.certified
    refused(label, needle)
    print(f"refused both paths after a changed {label}")

install(source)
at_zero.check()
away.check()
assert at_zero.certified and away.certified
print("restored source certified both paths again")
"""

CONTRACT_TEST = """\
import logos
import app


@logos.theorem(about=app.advance)
def advances(mid, *, result):
    return logos.contract(ensures=(result - mid == 1))


def test_advances():
    advances.check()
    assert advances.certified
    logos.export_proof(advances, "advance.logos")
"""

CONTRACT_STALE = """\
import pathlib
import types

import app
import logos
import pair_app
from logos.expr import Add, Lit, Var


@logos.theorem(about=app.advance)
def advance_contract(mid, *, result):
    return logos.contract(ensures=(result - mid == 1))


advance_contract.check()
assert advance_contract.certified
path = pathlib.Path(app.__file__)


def shrink(mid: int) -> int:
    return mid


original_code = app.advance.__code__
app.advance.__code__ = shrink.__code__.replace(co_filename=str(path))
assert not advance_contract.certified
for label, action in (
    ("check", advance_contract.check),
    ("export", lambda: logos.export_proof(advance_contract, "stale-code.logos")),
):
    try:
        action()
    except logos.LogosProofError as error:
        print(f"refused {label} after code change:", error)
    else:
        raise AssertionError(f"{label} accepted a stale code object")
assert not pathlib.Path("stale-code.logos").exists()
app.advance.__code__ = original_code
advance_contract.check()
assert advance_contract.certified

original_body = advance_contract.symbol.body
advance_contract.symbol.body = Add(Var("mid", int), Lit(2))
assert not advance_contract.certified
for label, action in (
    ("check", advance_contract.check),
    ("export", lambda: logos.export_proof(advance_contract, "stale-body.logos")),
):
    try:
        action()
    except logos.LogosProofError as error:
        print(f"refused {label} after body change:", error)
    else:
        raise AssertionError(f"{label} accepted a mutated translated body")
assert not pathlib.Path("stale-body.logos").exists()
advance_contract.symbol.body = original_body
advance_contract.check()
assert advance_contract.certified

source = path.read_text()
path.write_text("def advance(mid: int) -> int:\\n    return mid\\n")
assert not advance_contract.certified
for label, action in (
    ("check", advance_contract.check),
    ("export", lambda: logos.export_proof(advance_contract, "stale-source.logos")),
):
    try:
        action()
    except logos.LogosProofError as error:
        print(f"refused {label} after source change:", error)
    else:
        raise AssertionError(f"{label} accepted a stale source")
assert not pathlib.Path("stale-source.logos").exists()
path.write_text(source)
advance_contract.check()
assert advance_contract.certified


@logos.theorem(about=pair_app.first)
def first_is_x(x, y, *, result):
    return logos.contract(ensures=(result == x))


first_is_x.check()
assert first_is_x.certified
pair = pathlib.Path(pair_app.__file__)
pair_code = pair_app.first.__code__
swapped = "def first(y: int, x: int) -> int:\\n    return x\\n"
pair.write_text(swapped)
compiled = compile(swapped, str(pair), "exec")
pair_app.first.__code__ = next(
    value for value in compiled.co_consts
    if isinstance(value, types.CodeType) and value.co_name == "first"
)
assert not first_is_x.certified
try:
    first_is_x.check()
except logos.LogosContractError as error:
    print("refused parameter binding:", error)
else:
    raise AssertionError("reordered parameters were accepted")
pair.write_text("def first(x: int, y: int) -> int:\\n    return x\\n")
pair_app.first.__code__ = pair_code
first_is_x.check()
assert first_is_x.certified
print("same-process revalidation refused code, body, source and parameter order changes")
"""

CONTRACT_LIMITS = """\
import os
import sys
from pathlib import Path

import logos

import ambiguous_app
import branch_app
import global_app
import mismatch_app
import wrapper_app

before = set(Path(".").glob("*.logos"))


def refuse(label, fn, needle):
    try:
        @logos.theorem(about=fn)
        def claim(x, *, result):
            return logos.contract(ensures=(result - x == 1))
    except logos.LogosContractError as error:
        assert needle in str(error), (needle, str(error))
        print(f"{label}: {error}")
    else:
        raise AssertionError(f"{label} was accepted")


refuse("global", global_app.shift, "'OFFSET'")
refuse("branch", branch_app.choose, "single return statement")
refuse("wrapper", wrapper_app.wrapped, "wrapped or decorated")
refuse("ambiguous", ambiguous_app.twice, "2 times at module level")

path = Path(mismatch_app.__file__)
stat = path.stat()
path.write_text("def move(x: int) -> int:\\n    return x - 1\\n")
os.utime(path, ns=(stat.st_atime_ns, stat.st_mtime_ns))
assert path.stat().st_size == stat.st_size
refuse("mismatch", mismatch_app.move, "does not match the imported code object")

assert set(Path(".").glob("*.logos")) == before
print("no artifact exported by any refused contract")
"""

CONTRACT_LIMIT_MODULES = {
    "global_app.py": "OFFSET = 1\n\ndef shift(x: int) -> int:\n    return x + OFFSET\n",
    "branch_app.py": (
        "def choose(x: int) -> int:\n"
        "    if x:\n"
        "        return x + 1\n"
        "    return x\n"
    ),
    "wrapper_app.py": (
        "import functools\n\n"
        "def decorate(fn):\n"
        "    @functools.wraps(fn)\n"
        "    def wrapper(*args, **kwargs):\n"
        "        return fn(*args, **kwargs)\n"
        "    return wrapper\n\n"
        "@decorate\n"
        "def wrapped(x: int) -> int:\n"
        "    return x + 1\n"
    ),
    "ambiguous_app.py": (
        "def twice(x: int) -> int:\n    return x + 1\n\n"
        "def twice(x: int) -> int:\n    return x + 2\n"
    ),
    "mismatch_app.py": "def move(x: int) -> int:\n    return x + 1\n",
}


def fresh_source(path, text):
    """Replace source and invalidate bytecode, whatever its size or timestamp."""
    path.write_text(text)
    cache = path.parent / "__pycache__"
    shutil.rmtree(cache, ignore_errors=True)
    stamp = path.stat().st_mtime + 5
    os.utime(path, (stamp, stamp))
    assert not cache.exists()


def contracts(python, cold, recipient, evidence, env, offline):
    application = cold / "application"
    application.mkdir()
    app = application / "app.py"
    fresh_source(app, CONTRACT_APP)
    (application / "test_advance.py").write_text(CONTRACT_TEST)

    print("Contracts · pytest the installed wheel against a temporary application")
    passed = run([python, "-m", "pytest", "-q", "test_advance.py"], application, env=env)
    assert "1 passed" in passed.stdout

    artifact = application / "advance.logos"
    assert artifact.is_file()
    shutil.move(artifact, recipient / artifact.name)
    strict = replay(recipient, "check", "--strict", "advance.logos", offline=offline)
    assert "Verified with 0 custom axioms" in strict.stdout
    assert "result = " in strict.stdout and "advance" in strict.stdout
    inspected = replay(
        recipient, "inspect", "--json", "--strict", "advance.logos",
        offline=offline, show_output=False,
    )
    trace = json.loads(inspected.stdout)
    assert trace["status"] == "verified" and trace["custom_axioms"] == []
    [symbol] = trace["functions"]
    assert symbol["name"] == "advance" and symbol["params"] == ["int"]
    assert symbol["result"] == "int"
    assert symbol["body"] == {
        "tag": "add", "left": {"tag": "bound", "index": 0},
        "right": {"tag": "int", "value": "1"},
    }
    shutil.copy2(recipient / "advance.logos", evidence / "advance.logos")
    (evidence / "advance.inspect.json").write_text(inspected.stdout)

    print("Contracts · mutate the bound body and fail on the contract")
    original = app.stat()
    fresh_source(app, CONTRACT_MUTATED)
    assert app.stat().st_size != original.st_size
    failed = run([python, "-m", "pytest", "-q", "test_advance.py"], application,
                 env=env, code=1, show_output=False)
    output = failed.stdout + failed.stderr
    assert "1 failed" in output and "does not follow from its source body" in output
    print(output.strip().splitlines()[-1])
    (evidence / "advance-mutation.txt").write_text(output)

    print("Contracts · restore the body and pass again")
    fresh_source(app, CONTRACT_APP)
    restored = run([python, "-m", "pytest", "-q", "test_advance.py"], application, env=env)
    assert "1 passed" in restored.stdout

    print("Contracts · pytest and strict-check one equality branch per path")
    branch_application = cold / "branch_application"
    branch_application.mkdir()
    branch_app = branch_application / "app.py"
    fresh_source(branch_app, CONTRACT_BRANCH_APP)
    (branch_application / "test_branch.py").write_text(CONTRACT_BRANCH_TEST)
    branched = run(
        [python, "-m", "pytest", "-q", "test_branch.py"], branch_application, env=env
    )
    assert "1 passed" in branched.stdout
    for name in ("step_at_zero", "step_away_from_zero", "step_at_boundary"):
        artifact = branch_application / f"{name}.logos"
        assert artifact.is_file()
        shutil.move(artifact, recipient / artifact.name)
        strict = replay(recipient, "check", "--strict", artifact.name, offline=offline)
        assert "Verified with 0 custom axioms" in strict.stdout
        inspected = replay(
            recipient, "inspect", "--json", "--strict", artifact.name,
            offline=offline, show_output=False,
        )
        trace = json.loads(inspected.stdout)
        assert trace["status"] == "verified" and trace["custom_axioms"] == []
        [symbol] = trace["functions"]
        expected = "step[else]" if name == "step_away_from_zero" else "step[then]"
        assert symbol["name"] == expected
        shutil.copy2(recipient / artifact.name, evidence / artifact.name)
        (evidence / f"{name}.inspect.json").write_text(inspected.stdout)
    then_trace = json.loads((evidence / "step_at_zero.inspect.json").read_text())
    assert then_trace["functions"][0]["body"] == {"tag": "int", "value": "1"}
    else_trace = json.loads((evidence / "step_away_from_zero.inspect.json").read_text())
    assert else_trace["functions"][0]["body"] == {
        "tag": "add", "left": {"tag": "bound", "index": 0},
        "right": {"tag": "int", "value": "1"},
    }
    boundary_trace = json.loads((evidence / "step_at_boundary.inspect.json").read_text())
    assert "x = 0" in boundary_trace["statement_text"]

    print("Contracts · invalidate both paths after a changed guard or either branch")
    (branch_application / "stale_branch.py").write_text(CONTRACT_BRANCH_STALE)
    stale_branch = run([python, "stale_branch.py"], branch_application, env=env)
    assert "restored source certified both paths again" in stale_branch.stdout
    (evidence / "branch-stale.txt").write_text(stale_branch.stdout)

    print("Contracts · refuse source and statement gaps")
    limits = application / "limits"
    limits.mkdir()
    for name, text in CONTRACT_LIMIT_MODULES.items():
        (limits / name).write_text(text)
    (limits / "limits.py").write_text(CONTRACT_LIMITS)
    refused = run([python, "limits.py"], limits, env=env)
    assert "no artifact exported by any refused contract" in refused.stdout

    print("Contracts · revalidate code, translated body and source in one process")
    (application / "stale.py").write_text(CONTRACT_STALE)
    (application / "pair_app.py").write_text(CONTRACT_PAIR)
    stale = run([python, "stale.py"], application, env=env)
    assert "same-process revalidation refused code, body, source and parameter order changes" in stale.stdout
    (evidence / "advance-stale.txt").write_text(stale.stdout)


def order_contracts(python, cold, recipient, evidence, env, offline):
    application = cold / "order_application"
    application.mkdir()
    app = application / "app.py"
    fresh_source(app, ORDER_APP)
    (application / "test_order.py").write_text(ORDER_TEST)

    print("Order · pytest the installed wheel on both minimum paths and order laws")
    passed = run([python, "-m", "pytest", "-q", "test_order.py"], application, env=env)
    assert "1 passed" in passed.stdout

    for name in (
        "minimum_then", "minimum_else", "lt_add_transport", "lt_neq_from_lt",
    ):
        artifact = application / f"{name}.logos"
        assert artifact.is_file()
        shutil.move(artifact, recipient / artifact.name)
        strict = replay(recipient, "check", "--strict", artifact.name, offline=offline)
        assert "Verified with 0 custom axioms" in strict.stdout
        inspected = replay(
            recipient, "inspect", "--json", "--strict", artifact.name,
            offline=offline, show_output=False,
        )
        trace = json.loads(inspected.stdout)
        assert trace["status"] == "verified" and trace["custom_axioms"] == []
        if name.startswith("minimum"):
            [symbol] = trace["functions"]
            expected = "minimum[else]" if name == "minimum_else" else "minimum[then]"
            assert symbol["name"] == expected
            assert "not" in json.dumps(trace["statement"]) if name == "minimum_else" else True
        else:
            law = "lt_add" if name == "lt_add_transport" else "lt_neq"
            assert any(
                step.get("reference_id") == law and step["rule"] == "core_law"
                for step in trace["steps"]
            )
            assert all(step["rule"] != "axiom_ref" for step in trace["steps"])
        shutil.copy2(recipient / artifact.name, evidence / artifact.name)
        (evidence / f"{name}.inspect.json").write_text(inspected.stdout)

    print("Order · reject a reversed order-law instance in the installed checker")
    altered = json.loads((recipient / "lt_add_transport.logos").read_text())
    core = altered["proof"]
    while core["tag"] != "core_law":
        core = core.get("body", core.get("implication", core.get("proof")))
    core["args"] = [core["args"][1], core["args"][0], core["args"][2]]
    (recipient / "reversed-order.logos").write_text(json.dumps(altered))
    rejected = replay(
        recipient, "check", "--json", "reversed-order.logos", offline=offline,
        code=1, show_output=False,
    )
    diagnostic = json.loads(rejected.stderr)["error"]
    assert (
        "antecedent does not match premise" in diagnostic
        or "proof conclusion mismatch" in diagnostic
    )

    print("Order · invalidate both paths after a guard or branch change")
    (application / "stale_order.py").write_text(ORDER_STALE)
    stale = run([python, "stale_order.py"], application, env=env)
    assert "order guard and branch mutations invalidated both paths and restored" in stale.stdout
    (evidence / "order-stale.txt").write_text(stale.stdout)


def primes(python, cold, recipient, evidence, env, offline):
    print(f"Primes · replay Euclid's theorem and rebuild it, then {offline and 'isolated replay' or 'clean-PATH replay'}")
    run(["logos", "example", "primes"], cold, env=env)
    emitted = (cold / "primes.py").read_bytes()
    bundled = (FIXTURES.parents[2] / "examples/primes.py").read_bytes()
    assert emitted == bundled, "the installed example differs from the bundled source"
    shutil.copy2(cold / "primes.logos", recipient / "primes.logos")

    verdict = replay(recipient, "check", "--strict", "primes.logos", offline=offline)
    assert "Verified with 0 custom axioms" in verdict.stdout
    assert "∃p:int" in verdict.stdout
    inspected = json.loads(replay(
        recipient, "inspect", "--json", "--strict", "primes.logos", offline=offline
    ).stdout)
    assert inspected["status"] == "verified"
    assert inspected["custom_axioms"] == []
    assert inspected["theory"] == "logos-core-v1"
    rendered = replay(
        recipient, "inspect", "--markdown", "--strict", "primes.logos", offline=offline
    ).stdout
    assert "infinitely_many_primes" in rendered or "strict" in rendered.lower()

    # Rebuild the certificate from the installed wheel and require identical bytes.
    run([str(python), "primes.py", "authored-primes.logos"], cold, env=env)
    assert (cold / "authored-primes.logos").read_bytes() == (cold / "primes.logos").read_bytes()
    shutil.copy2(cold / "authored-primes.logos", recipient / "authored-primes.logos")
    replay(recipient, "check", "--strict", "authored-primes.logos", offline=offline)

    # A forged target must be rejected even with the genuine proof bytes.
    forged = json.loads((cold / "primes.logos").read_text())
    target = forged["target"]
    statement = target["body"]["right"]
    conclusion = statement["body"]
    order = conclusion["right"]
    order["left"], order["right"] = order["right"], order["left"]
    (cold / "forged-primes.logos").write_text(json.dumps(forged))
    shutil.copy2(cold / "forged-primes.logos", recipient / "forged-primes.logos")
    forged_error = replay(recipient, "check", "--strict", "forged-primes.logos",
                          offline=offline, code=1)
    assert "proof conclusion mismatch" in forged_error.stderr

    (evidence / "primes.logos").write_bytes((cold / "primes.logos").read_bytes())
    (evidence / "authored-primes.logos").write_bytes((cold / "authored-primes.logos").read_bytes())
    (evidence / "primes.md").write_text(rendered)
    (evidence / "primes.json").write_text(json.dumps(inspected, indent=2))


def binary_search_contract(python, cold, recipient, evidence, env, offline):
    application = cold / "binary_search_application"
    application.mkdir()
    source = (Path(__file__).resolve().parents[1] / "examples/binary_search.py").read_text()
    (application / "binary_search.py").write_text(source)
    print("Binary search · author the loop contract with the installed wheel")
    run(["python", "binary_search.py"], application, env=env)
    shutil.move(application / "binary_search.logos", recipient / "binary_search.logos")
    shutil.copy2(application / "binary_search.py", evidence / "binary_search.py")

    print(f"Binary search · strict replay and machine inspection, then an offline replay")
    check = replay(recipient, "check", "--strict", "binary_search.logos", offline=offline)
    assert "Verified with 0 custom axioms" in check.stdout
    inspected = json.loads(replay(
        recipient, "inspect", "--json", "--strict", "binary_search.logos", offline=offline
    ).stdout)
    assert inspected["status"] == "verified"
    assert inspected["custom_axioms"] == []

    wrong = source.replace("(low + high) // 2", "(low + high + 1) // 2")
    (application / "wrong_midpoint.py").write_text(wrong)
    rejected = run(["python", "wrong_midpoint.py"], application, env=env, code=1)
    assert "LogosProofError" in rejected.stderr or "cannot prove" in rejected.stderr

    data = json.loads((recipient / "binary_search.logos").read_text())
    for statement in data["programs"][0]["body"]:
        if statement.get("tag") == "while":
            for item in statement["body"]:
                if item.get("tag") == "if":
                    for assignment in item["then_body"]:
                        if assignment.get("tag") == "assign":
                            assignment["value"] = {"tag": "int", "value": "0"}
                            break
    (recipient / "forged-binary-search.logos").write_text(json.dumps(data))
    forged = replay(
        recipient, "check", "--json", "forged-binary-search.logos",
        offline=offline, code=1, show_output=False,
    )
    assert "error" in json.loads(forged.stderr)
    data = json.loads((recipient / "binary_search.logos").read_text())
    data["programs"][0]["obligations"].pop(0)
    (recipient / "missing-binary-search.logos").write_text(json.dumps(data))
    missing = replay(
        recipient, "check", "--json", "missing-binary-search.logos",
        offline=offline, code=1, show_output=False,
    )
    assert "missing proof" in json.loads(missing.stderr)["error"]
    for artifact in ("binary_search.logos", "forged-binary-search.logos",
                     "missing-binary-search.logos"):
        shutil.copy2(recipient / artifact, evidence / artifact)


BOOK = Path(__file__).resolve().parents[1] / "book"

BOOK_FAILURE = """\
import json
import runpy
import sys

import logos

try:
    runpy.run_path(sys.argv[1], run_name="__main__")
except logos.LogosProofError as error:
    print(json.dumps(error.details, ensure_ascii=False))
    raise SystemExit(1)
else:
    raise SystemExit(0)
"""

BOOK_NEGATIVES = """\
import json
import logos
from logos import Int, Prop, exists
from logos.expr import Var


@logos.theorem
def first_fact(P: Prop, Q: Prop):
    return (P & Q) >> P


@first_fact.proof
def prove_first(p, P, Q):
    both = p.assume(P & Q)
    return both.right()


@logos.definition
def zdivides(d: Int, a: Int):
    return exists(Int, lambda k: a == d * k)


@logos.theorem
def wrong_witness(d: Int, a: Int):
    return (zdivides(d, a) & zdivides(d, a + 1)) >> zdivides(d, 1)


@wrong_witness.proof
def prove_wrong(p, d, a):
    h = p.assume(zdivides(d, a) & zdivides(d, a + 1))
    k, left = p.obtain(h.left())
    j, right = p.obtain(h.right())
    quotient = j - k
    one = p.ring(1 == d * quotient, using=[left, right])
    return p.witness(k - j, one)


@logos.theorem
def escaped_witness(d: Int, a: Int):
    return (zdivides(d, a) & zdivides(d, a + 1)) >> zdivides(d, 1)


@escaped_witness.proof
def prove_escape(p, d, a):
    h = p.assume(zdivides(d, a) & zdivides(d, a + 1))
    k, left = p.obtain(h.left())
    j, right = p.obtain(h.right())
    quotient = j - k
    one = p.ring(1 == d * quotient, using=[left, right])
    outside = Var("outside", int)
    return p.witness(outside, one)


kinds = {}
for theorem in (first_fact, wrong_witness, escaped_witness):
    try:
        theorem._run_proof(theorem.statement)
    except logos.LogosProofError as error:
        kinds[theorem.name] = error.details
    else:
        raise AssertionError(f"{theorem.name} was accepted")
print(json.dumps(kinds, ensure_ascii=False))
"""


def book(python, cold, recipient, evidence, env, offline):
    """Tangle the Spanish page and run it from the installed wheel."""
    scriptorium = python.parent / "scriptorium"
    assert scriptorium.exists(), "install Scriptorium in the author environment"
    page = BOOK / "vecinos.md"
    source = page.read_text(encoding="utf-8")

    room = cold / "book"
    room.mkdir()
    (room / "vecinos.md").write_text(source, encoding="utf-8")
    run([scriptorium, "tangle", "vecinos.md"], room, env=env)
    run([scriptorium, "tangle", "--test", "vecinos.md"], room, env=env)
    run([python, "vecinos.py"], room, env=env)
    assert (room / "vecinos.logos").exists()

    shutil.copy2(room / "vecinos.logos", recipient / "vecinos.logos")
    verdict = replay(recipient, "check", "--strict", "vecinos.logos", offline=offline)
    assert "Verified with 0 custom axioms" in verdict.stdout
    assert "common_divisor" in verdict.stdout
    inspected = json.loads(replay(
        recipient, "inspect", "--json", "--strict", "vecinos.logos", offline=offline
    ).stdout)
    assert inspected["status"] == "verified"
    assert inspected["custom_axioms"] == []
    shutil.copy2(room / "vecinos.py", evidence / "vecinos.py")
    shutil.copy2(room / "vecinos.logos", evidence / "vecinos.logos")

    assert source.count("    quotient = j - k") == 1
    broken = source.replace("    quotient = j - k", "    quotient = k - j", 1)
    broken_dir = cold / "book-broken"
    broken_dir.mkdir()
    (broken_dir / "vecinos.md").write_text(broken, encoding="utf-8")
    run([scriptorium, "tangle", "vecinos.md"], broken_dir, env=env)
    failure = run(
        [python, "-c", BOOK_FAILURE, "vecinos.py"], broken_dir, env=env, code=1
    )
    details = json.loads(failure.stdout.strip().splitlines()[-1])
    generated = (broken_dir / "vecinos.py").read_text(encoding="utf-8").splitlines()
    inverted = next(
        number for number, line in enumerate(generated, 1)
        if line.strip() == "quotient = k - j"
    )
    markdown = broken.splitlines()
    markdown_line = next(
        number for number, line in enumerate(markdown, 1)
        if line.strip() == "quotient = k - j"
    )
    assert details["kind"] == "ring_goal_unreachable"
    assert details["goal"]["text"] == "1 = d * (k - j)"
    assert [item["label"] for item in details["opened"]] == ["left", "right"]
    assert details["opened"][0]["statement"]["text"] == "a = d * k"
    assert details["opened"][1]["statement"]["text"] == "a + 1 = d * j"
    assert any(item["line"] == inverted for item in details["related"])
    human = run([python, "vecinos.py"], broken_dir, env=env, code=1)
    assert "expected goal: 1 = d * (k - j)" in human.stderr
    assert "left: a = d * k" in human.stderr
    assert "right: a + 1 = d * j" in human.stderr
    report = {
        "markdown_file": "vecinos.md",
        "markdown_line": markdown_line,
        "generated_file": "vecinos.py",
        "failed_step_line": details["line"],
        "inverted_assignment_line": inverted,
        "details": details,
    }
    (evidence / "book-sign-failure.txt").write_text(human.stderr, encoding="utf-8")
    (evidence / "book-failure-report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    shutil.copy2(broken_dir / "vecinos.py", evidence / "vecinos-broken.py")

    # Recover by restoring the sign and running the same three commands.
    recovered = cold / "book-recovered"
    recovered.mkdir()
    (recovered / "vecinos.md").write_text(source, encoding="utf-8")
    run([scriptorium, "tangle", "vecinos.md"], recovered, env=env)
    run([python, "vecinos.py"], recovered, env=env)
    replay(recipient, "check", "--strict", "vecinos.logos", offline=offline)

    negatives = cold / "book-negatives.py"
    negatives.write_text(BOOK_NEGATIVES, encoding="utf-8")
    result = run([python, str(negatives)], cold, env=env)
    kinds = json.loads(result.stdout)
    assert kinds["first_fact"]["kind"] == "proof_mismatch"
    assert kinds["first_fact"]["source_line"] == "return both.right()"
    assert kinds["wrong_witness"]["kind"] == "witness_mismatch"
    assert kinds["wrong_witness"]["expected"]["text"] == "1 = d * (k - j)"
    assert kinds["wrong_witness"]["got"]["text"] == "1 = d * (j - k)"
    assert kinds["escaped_witness"]["kind"] == "witness_escape"
    assert kinds["escaped_witness"]["unbound"] == ["outside"]
    (evidence / "book-authoring-negatives.json").write_text(
        json.dumps(kinds, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print("book lesson: tangle, strict certificate, sign failure, recovery, negatives")


def book_euclid(python, cold, recipient, evidence, env, offline):
    """Tangle the Spanish Euclid chapter and replay its complete derivation."""
    scriptorium = python.parent / "scriptorium"
    assert scriptorium.exists(), "install Scriptorium in the author environment"
    page = BOOK / "euclides.md"
    source = page.read_text(encoding="utf-8")

    room = cold / "euclides"
    room.mkdir()
    (room / "euclides.md").write_text(source, encoding="utf-8")
    run([scriptorium, "tangle", "euclides.md"], room, env=env)
    run([scriptorium, "tangle", "--test", "euclides.md"], room, env=env)
    run([python, "euclides.py"], room, env=env)
    assert (room / "euclides.logos").exists()

    shutil.copy2(room / "euclides.logos", recipient / "euclides.logos")
    verdict = replay(recipient, "check", "--strict", "euclides.logos", offline=offline)
    assert "Verified with 0 custom axioms" in verdict.stdout
    assert "euclid" in verdict.stdout
    inspected = json.loads(replay(
        recipient, "inspect", "--json", "--strict", "euclides.logos", offline=offline
    ).stdout)
    assert inspected["status"] == "verified"
    assert inspected["custom_axioms"] == []
    shutil.copy2(room / "euclides.py", evidence / "euclides.py")
    shutil.copy2(room / "euclides.logos", evidence / "euclides.logos")

    assert source.count("    m = f + 1") == 1
    broken = source.replace("    m = f + 1", "    m = f", 1)
    broken_dir = cold / "euclides-broken"
    broken_dir.mkdir()
    (broken_dir / "euclides.md").write_text(broken, encoding="utf-8")
    run([scriptorium, "tangle", "euclides.md"], broken_dir, env=env)
    failure = run(
        [python, "-c", BOOK_FAILURE, "euclides.py"], broken_dir, env=env, code=1
    )
    details = json.loads(failure.stdout.strip().splitlines()[-1])
    assert details["kind"] == "apply_premise_mismatch"
    assert details["lemma"] == "common_divisor"
    assert details["source_line"].startswith("divides_one = p.apply(common_divisor")
    assert "factorial(n) + 1" in details["expected"]["text"]
    assert details["got"]["text"].count("factorial(n) = q * k") == 2
    assert not (broken_dir / "euclides.logos").exists()
    human = run([python, "euclides.py"], broken_dir, env=env, code=1)
    assert "needed by common_divisor" in human.stderr
    assert "expected:" in human.stderr and "got:" in human.stderr
    assert "failing source: divides_one = p.apply(common_divisor" in human.stderr
    (evidence / "euclides-mutation.txt").write_text(human.stderr, encoding="utf-8")
    shutil.copy2(broken_dir / "euclides.py", evidence / "euclides-broken.py")

    recovered = cold / "euclides-recovered"
    recovered.mkdir()
    (recovered / "euclides.md").write_text(source, encoding="utf-8")
    run([scriptorium, "tangle", "euclides.md"], recovered, env=env)
    run([python, "euclides.py"], recovered, env=env)
    replay(recipient, "check", "--strict", "euclides.logos", offline=offline)
    print("euclides lesson: tangle, strict certificate, bound mutation, recovery")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("python", type=Path)
    parser.add_argument("evidence", type=Path)
    parser.add_argument("--offline", action="store_true", help="isolate replay with Linux bubblewrap")
    options = parser.parse_args()
    binary, python = options.binary.absolute(), options.python.absolute()
    evidence = options.evidence.absolute()
    evidence.mkdir(parents=True, exist_ok=True)
    env = {"PATH": os.pathsep.join(map(str, [binary.parent, python.parent]))}
    isolation = (
        "network-isolated replay (bubblewrap: unshared network, empty filesystem)"
        if options.offline
        else "clean-PATH replay (empty PATH, shared filesystem and network)"
    )
    print(f"Installed smoke · scripted authoring, {isolation}; independent trial is separate")

    with tempfile.TemporaryDirectory(prefix="logos-installed-") as temp:
        clean = Path(temp)
        author = clean / "author"
        author.mkdir()
        recipient = clean / "recipient"
        recipient.mkdir()
        shutil.copy2(binary, recipient / "logos")
        shutil.copy2(FIXTURES / "authorization.logos", recipient / "authorization.logos")

        print(f"P1 · {isolation}")
        verdict = replay(recipient, "check", "authorization.logos", offline=options.offline)
        assert f"Statement   {EXPECTED}" in verdict.stdout
        assert "Theory      logos-core-v1" in verdict.stdout
        assert "Verified with 0 custom axioms" in verdict.stdout
        replay(recipient, "check", "--strict", "authorization.logos", offline=options.offline)
        hand_written = json.loads(replay(
            recipient, "inspect", "--json", "authorization.logos", offline=options.offline
        ).stdout)
        assert hand_written["custom_axioms"] == []
        assert hand_written["steps"][-1]["discharged"] == "proof.assumption"

        print("P2 · rejection and declaration identity")
        for fixture, diagnostic in [
            ("wrong-projection", "proof conclusion mismatch"),
            ("out-of-scope", "out-of-scope hypothesis"),
            ("unsupported-version", "unsupported proof format"),
            ("duplicate-declaration", "duplicate declaration ID"),
            ("malformed-conjunction", "malformed proof file"),
            ("wrong-sort", "has sort int, expected prop"),
        ]:
            shutil.copy2(FIXTURES / f"{fixture}.logos", author)
            error = run(["logos", "inspect", "--json", f"{fixture}.logos"], author, env=env, code=1)
            assert not error.stdout
            diagnostic_text = json.loads(error.stderr)["error"]
            assert diagnostic in diagnostic_text
            if fixture == "wrong-projection":
                assert f"Expected: {EXPECTED}" in diagnostic_text
                assert "Derived:  (Authenticated ∧ Authorized) → Authenticated" in diagnostic_text
        shutil.copy2(FIXTURES / "shared-label.logos", author)
        shared = json.loads(run(["logos", "check", "--json", "shared-label.logos"], author, env=env).stdout)
        assert [item["name"] for item in shared["declarations"]] == ["Permission", "Permission"]
        assert shared["statement"]["left"]["left"]["id"] == "p1"
        assert shared["statement"]["right"]["id"] == "p2"

        print("P4 · discovery from installed help")
        cold = clean / "cold"
        cold.mkdir()
        help_text = run(["logos", "--help"], cold, env=env).stdout
        inspect_help = run(["logos", "inspect", "--help"], cold, env=env).stdout
        assert "State the claim, then introduce the variables and hypotheses" in inspect_help
        assert "Group routine rewrites into equations" in inspect_help
        assert "Explain the final conversion" in inspect_help
        assert "Omit internal step IDs" in inspect_help
        commands = help_text.split("From an empty directory:\n")[1].split("\n\n")[0].splitlines()
        author_commands = help_text.split("then run:\n")[1].split("\n\n")[0].splitlines()
        for line in [*commands, *author_commands]:
            reply = run(shlex.split(line), cold, env=env)
            if line.strip() == "logos commands --json":
                contract = json.loads(reply.stdout)
                assert contract["protocol_version"] == 1
                assert contract["proof_formats"] == ["logos-proof-v1"]
                assert "steps" in contract["commands"]["inspect"]
                guidance = " ".join(contract["commands"]["inspect"]["human_proof_guidance"])
                assert "Group routine rewrites" in guidance and "Omit internal step IDs" in guidance
                assert "1" in contract["exit_codes"]
                assert "3" in contract["exit_codes"]
                for operation in ("check", "inspect"):
                    assert "--strict" in contract["commands"][operation]["flags"]
                assert "theorem_ref" in contract["proof_format"]["evidence"]
                assert "axiom_ref" in contract["proof_format"]["evidence"]
        run(
            ["python", "-c", "import logos; print(logos.__file__); "
             "assert 'site-packages' in logos.__file__"],
            cold, env=env,
        )

        print(f"P3 · remove the author module before {isolation}")
        (cold / "authorization.py").unlink()
        shutil.move(cold / "authored.logos", recipient / "authored.logos")
        authored = json.loads(replay(
            recipient, "inspect", "--json", "authored.logos", offline=options.offline
        ).stdout)
        for field in ("theory", "declarations", "statement", "statement_text", "custom_axioms", "steps"):
            assert authored[field] == hand_written[field]
        assert authored["artifact_sha256"] != hand_written["artifact_sha256"]
        shutil.copy2(recipient / "authored.logos", evidence / "authored.logos")
        p5 = evidence / "recipient"
        p5.mkdir(exist_ok=True)
        shutil.copy2(recipient / "logos", p5 / "logos")
        shutil.copy2(recipient / "authored.logos", p5 / "authorization.logos")

        print("P4 · scripted author smoke after discovery (not an independent trial)")
        (cold / "cold_author.py").write_text(COLD_AUTHOR)
        run(["python", "cold_author.py"], cold, env=env)
        checked = json.loads(run(["logos", "inspect", "--json", "cold.logos"], cold, env=env).stdout)
        assert checked["statement"] == hand_written["statement"]
        assert checked["custom_axioms"] == []
        assert checked["steps"][-1]["binder"] == "permission"
        shutil.copy2(cold / "cold_author.py", evidence / "cold_author.py")
        shutil.copy2(cold / "cold.logos", evidence / "cold.logos")

        print(f"Dependencies · discover and author, then {isolation}")
        heading = "To replay a result that uses a checked lemma and one custom axiom:\n"
        commands = help_text.split(heading)[1].split("\n\n")[0].splitlines()
        for line in commands:
            argv = shlex.split(line)
            run(argv, cold, env=env, code=3 if "--strict" in argv else 0)
        (cold / "dependencies.py").unlink()
        for filename in ("dependencies.logos", "authored-dependencies.logos"):
            shutil.move(cold / filename, recipient / filename)
        reference = json.loads(replay(
            recipient, "inspect", "--json", "dependencies.logos", offline=options.offline
        ).stdout)
        filename = "authored-dependencies.logos"
        conditional = json.loads(replay(
            recipient, "inspect", "--json", filename, offline=options.offline
        ).stdout)
        for field in ("theory", "declarations", "statement", "statement_text", "custom_axioms", "steps"):
            assert conditional[field] == reference[field]
        assert conditional["statement_text"] == "Q"
        [used] = conditional["custom_axioms"]
        assert used["id"] == "A"
        assert used["statement_text"] == 'P["p2"]:prop ∧ Q["p1"]:prop'
        assert used["path"] == ["proof", 'lemma["L"].proof', 'lemma["L"].proof.proof']

        changed = json.loads((recipient / filename).read_text())
        changed["lemmas"][0]["proof"]["tag"] = "and_elim_l"
        (recipient / "invalid-dependencies.logos").write_text(json.dumps(changed))
        for operation in ("check", "inspect"):
            denied = replay(recipient, operation, "--json", "--strict", filename,
                            offline=options.offline, code=3)
            policy = json.loads(denied.stdout)
            assert policy["status"] == "policy_denied"
            assert policy["custom_axioms"] == [used]
            assert ("steps" in policy) == (operation == "inspect")
            old_flag = replay(recipient, operation, "--deny-custom-axioms", filename,
                              offline=options.offline, code=2)
            assert "unexpected argument" in old_flag.stderr
            for flags in ([], ["--strict"]):
                invalid = replay(recipient, operation, "--json", *flags, "invalid-dependencies.logos",
                                 offline=options.offline, code=1)
                assert not invalid.stdout
                error = json.loads(invalid.stderr)
                assert error["status"] == "error" and "proof conclusion mismatch" in error["error"]
        for artifact in ("dependencies.logos", filename, "invalid-dependencies.logos"):
            shutil.copy2(recipient / artifact, evidence / artifact)

        print(f"Arithmetic · export from the installed wheel, then {isolation}")
        arithmetic(cold, recipient, evidence, help_text, env, options.offline)

        print(f"Existentials · export a successor proof from the installed wheel, then {isolation}")
        existentials(cold, recipient, evidence, env, options.offline)

        print(f"Markdown · render checked evidence in {isolation}")
        markdown(recipient, evidence, options.offline)

        print(f"Knights and Knaves · check scoped cases in {isolation}")
        knights_knaves(python, cold, recipient, evidence, env, options.offline)

        print(f"Domain solve · discover from installed help, then {isolation}")
        solve_knights_knaves(cold, recipient, evidence, help_text, env, options.offline)

        print(f"Function contracts · bind source, mutate and refuse, then {isolation}")
        contracts(python, cold, recipient, evidence, env, options.offline)

        print(f"Strict order · prove both minimum paths and order laws, then {isolation}")
        order_contracts(python, cold, recipient, evidence, env, options.offline)

        print(f"Binary search · prove total correctness, then {isolation}")
        binary_search_contract(python, cold, recipient, evidence, env, options.offline)

        print(f"Primes · check Euclid's theorem and rebuild it, then {isolation}")
        primes(python, cold, recipient, evidence, env, options.offline)

        print(f"Book lesson · tangle the Spanish page and exercise the authoring layer, then {isolation}")
        book(python, cold, recipient, evidence, env, options.offline)

        print(f"Euclid book lesson · tangle the full chapter, then {isolation}")
        book_euclid(python, cold, recipient, evidence, env, options.offline)

    print("16 acceptance stages exercised")


if __name__ == "__main__":
    main()
