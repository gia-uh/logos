import hashlib
import json
import shutil
import subprocess

import pytest

import logos
from logos.kernel import AndElimL, AndElimR, HypRef, ImpliesIntro
from logos.tactics import apply, exact, intro


pytestmark = pytest.mark.skipif(shutil.which("logos") is None, reason="install the Rust logos CLI")
EXPECTED = "(Authenticated ∧ Authorized) → Authorized"
DERIVED = "(Authenticated ∧ Authorized) → Authenticated"


def project_authorized(goal):
    return AndElimR(HypRef("h"))


def project_authenticated(goal):
    return AndElimL(HypRef("h"))


def prepared(kind):
    authenticated = logos.var("Authenticated", bool)
    authorized = logos.var("Authorized", bool)
    statement = (authenticated & authorized) >> authorized
    proof = [intro("h"), project_authorized]
    if kind == "named":
        @logos.theorem
        def authorization():
            return statement

        return authorization.proof(proof)
    return logos.prove(statement, proof)


@pytest.fixture
def invocations(monkeypatch):
    seen = []
    run = subprocess.run

    def record(argv, **kwargs):
        result = run(argv, **kwargs)
        if argv[1] == "check":
            seen.append((argv, kwargs["input"], result))
        return result

    monkeypatch.setattr(logos.portable.subprocess, "run", record)
    return seen


@pytest.mark.parametrize("kind", ["named", "anonymous"])
def test_checked_artifact_is_current_for_its_exact_evidence(kind, tmp_path, invocations):
    proof = prepared(kind)
    assert logos.check(proof) is proof
    receipt = logos.export_proof(proof, tmp_path / "checked.logos")
    assert proof.certified
    assert proof.receipt is receipt
    assert (tmp_path / "checked.logos").read_bytes() == receipt.artifact
    assert receipt.artifact_sha256 == hashlib.sha256(receipt.artifact).hexdigest()
    assert len(invocations) == 1
    assert invocations[0][1] == receipt.artifact
    assert invocations[0][2].returncode == 0

    # Mutate the original attachment in place with statement and context fixed.
    proof._proof_spec[1] = project_authenticated
    assert not proof.certified
    with pytest.raises(logos.LogosProofError, match="proof conclusion mismatch") as failure:
        logos.check(proof)
    assert EXPECTED in str(failure.value)
    assert DERIVED in str(failure.value)
    assert len(invocations) == 2
    first, wrong = (json.loads(call[1]) for call in invocations)
    first["proof"]["body"]["tag"] = "and_elim_l"
    assert wrong == first
    assert invocations[-1][2].returncode == 1
    assert invocations[-1][2].stdout == b""
    assert not proof.certified
    with pytest.raises(logos.LogosProofError, match="no current Rust verification"):
        logos.export_proof(proof, tmp_path / "wrong.logos")
    assert not (tmp_path / "wrong.logos").exists()
    assert (tmp_path / "checked.logos").read_bytes() == receipt.artifact


@pytest.mark.parametrize("kind", ["named", "anonymous", "automatic"])
@pytest.mark.parametrize("change", ["undeclared", "wrong-sort"])
def test_changed_declaration_context_clears_verification(kind, change, invocations):
    proof = prepared("named" if kind == "automatic" else kind)
    check = logos.prove if kind == "automatic" else logos.check
    assert check(proof).certified
    receipt = proof.receipt

    authenticated, authorized = proof.declarations
    if change == "undeclared":
        proof.declarations = (authorized,)
        diagnostic = "undeclared proposition"
    else:
        authenticated.type = int
        diagnostic = "has sort int, expected prop"
    assert not proof.certified
    with pytest.raises(logos.LogosProofError, match=diagnostic):
        check(proof)
    assert proof.receipt is None
    assert json.loads(receipt.artifact)["declarations"][0]["sort"] == "prop"
    if change == "undeclared":
        assert len(invocations) == 1  # Export rejects the unresolved symbol.
    else:
        assert len(invocations) == 2
        assert invocations[-1][2].returncode == 1
        original = json.loads(invocations[0][1])
        changed = json.loads(invocations[-1][1])
        assert original["target"] == changed["target"]
        if kind != "automatic":
            assert original["proof"] == changed["proof"]


@pytest.mark.parametrize("kind", ["named", "anonymous"])
def test_statement_mutation_and_recheck(kind, invocations):
    proof = prepared(kind)
    logos.check(proof)
    old = proof.receipt
    # Mutate the existing statement object, keeping its context and tactics.
    proof.statement.consequent = proof.declarations[0]
    assert not proof.certified
    with pytest.raises(logos.LogosProofError, match="proof conclusion mismatch"):
        logos.check(proof)
    assert proof.receipt is None
    assert old.artifact_sha256 != hashlib.sha256(invocations[-1][1]).hexdigest()


def test_automatic_replacement_needs_a_new_rust_check(invocations):
    proof = prepared("named")
    logos.prove(proof)
    original = proof.receipt
    evidence = proof._evidence
    proof._evidence = ImpliesIntro(evidence.hyp, evidence.hyp_name, AndElimL(HypRef(evidence.hyp_name)))
    assert not proof.certified
    assert logos.prove(proof).certified
    replacement = proof.receipt
    assert original.artifact_sha256 != replacement.artifact_sha256
    assert len(invocations) == 2
    assert invocations[-1][0][1:] == ["check", "--json", "--deny-custom-axioms", "-"]
    assert invocations[-1][1] == replacement.artifact
    verdict = json.loads(invocations[-1][2].stdout)
    assert verdict["artifact_sha256"] == replacement.artifact_sha256
    assert verdict["statement_text"] == EXPECTED


def test_rejects_external_dependencies_even_with_stale_flags(invocations):
    dependency = prepared("named")
    logos.check(dependency)
    dependency.__dict__["certified"] = True
    dependency.statement.consequent = dependency.declarations[0]
    assert not dependency.certified
    target = logos.Theorem(dependency.statement, name="via_theorem").proof(apply(dependency))
    axiom = logos.Axiom(dependency.statement, name="external_axiom")
    axiom.certified = True
    via_axiom = logos.prove(dependency.statement, [apply(axiom)])
    with pytest.raises(logos.LogosProofError, match="portable theorem dependency"):
        logos.check(target)
    with pytest.raises(logos.LogosProofError, match="unsupported portable proof term Axiom"):
        logos.check(via_axiom)
    assert len(invocations) == 1
    assert not target.certified and not via_axiom.certified


def test_local_apply_is_scoped_and_checks(invocations):
    a = logos.var("Authenticated", bool)
    proof = logos.prove(a >> a, [intro("h"), apply("h")])
    assert logos.check(proof).certified
    assert json.loads(invocations[-1][2].stdout)["statement_text"] == "Authenticated → Authenticated"
    outside = logos.prove(a, [exact(HypRef("h"))])
    with pytest.raises(logos.LogosProofError, match="out-of-scope hypothesis"):
        logos.check(outside)
    assert not outside.certified


def test_recheck_fails_closed_without_the_executable(monkeypatch):
    proof = logos.check(prepared("named"))
    monkeypatch.setenv("PATH", "")
    with pytest.raises(logos.LogosProofError, match="not found on PATH"):
        logos.check(proof)
    assert not proof.certified


def test_recheck_rejects_an_unsupported_protocol(monkeypatch, tmp_path):
    proof = logos.check(prepared("named"))
    incompatible = tmp_path / "logos"
    incompatible.write_text('#!/bin/sh\nprintf \'%s\\n\' \'{"protocol_version":99}\'\n')
    incompatible.chmod(0o755)
    monkeypatch.setenv("PATH", str(tmp_path))
    with pytest.raises(logos.LogosProofError, match="unsupported Rust logos commands protocol"):
        logos.check(proof)
    assert not proof.certified
