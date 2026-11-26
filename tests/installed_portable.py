"""Exercise P1–P4 and dependencies with an installed binary and wheel.

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


def run(argv, cwd, *, env=None, code=0):
    print(f"$ {shlex.join(str(arg) for arg in argv)}", flush=True)
    result = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True)
    print(result.stdout, end="")
    print(result.stderr, end="")
    print(f"exit {result.returncode}", flush=True)
    assert result.returncode == code
    return result


def replay(recipient, *args, offline, code=0):
    if not offline:
        return run(["./logos", *args], recipient, env={"PATH": ""}, code=code)

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
    return run([*command, "--chdir", "/", "--", "/logos", *args], recipient, code=code)


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
        commands = help_text.split("From an empty directory:\n")[1].split("\n\n")[0].splitlines()
        author_commands = help_text.split("then run:\n")[1].split("\n\n")[0].splitlines()
        for line in [*commands, *author_commands]:
            reply = run(shlex.split(line), cold, env=env)
            if line.strip() == "logos commands --json":
                contract = json.loads(reply.stdout)
                assert contract["protocol_version"] == 1
                assert contract["proof_formats"] == ["logos-proof-v1"]
                assert "steps" in contract["commands"]["inspect"]
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

    print("5 acceptance stages exercised")


if __name__ == "__main__":
    main()
