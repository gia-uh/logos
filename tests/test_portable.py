import hashlib
import json
import shutil
import subprocess

import pytest

import logos
from logos.kernel import (
    AndElimL, AndElimR, AndIntro, AxiomRef, CaseAnalysis, ExFalso, HypRef,
    ImpliesElim, ImpliesIntro, NotElim, NotIntro, OrIntroL, OrIntroR,
)
from logos.tactics import (
    apply, assumption, cases, contradiction, exact, have, intro, left, right, split,
)


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
    assert invocations[-1][0][1:] == ["check", "--json", "-"]
    assert invocations[-1][1] == replacement.artifact
    verdict = json.loads(invocations[-1][2].stdout)
    assert verdict["artifact_sha256"] == replacement.artifact_sha256
    assert verdict["statement_text"] == EXPECTED


def test_stale_theorem_flag_does_not_bypass_lemma_verification(invocations):
    dependency = prepared("named")
    logos.check(dependency)
    dependency.__dict__["certified"] = True
    dependency.statement.consequent = dependency.declarations[0]
    assert not dependency.certified
    target = logos.Theorem(dependency.statement, name="via_theorem").proof(apply(dependency))
    with pytest.raises(logos.LogosProofError, match=r'lemma\["authorization"\].*proof conclusion mismatch'):
        logos.check(target)
    assert len(invocations) == 2
    assert invocations[-1][2].returncode == 1
    assert not target.certified


def dependency_bundle():
    p, q = logos.vars("P Q", bool)
    axiom = logos.Axiom(p & q, name="A")
    lemma = logos.Theorem(q, name="L").proof(exact(AndElimR(AxiomRef(axiom))))
    target = logos.Theorem(q, name="T").proof(apply(lemma))
    return p, q, axiom, lemma, target


@pytest.mark.parametrize("change", ["axiom-statement", "lemma-attachment", "lemma-term"])
def test_transitive_mutation_clears_current_certification_before_recheck(change, tmp_path, invocations):
    p, q, axiom, lemma, target = dependency_bundle()
    logos.check(lemma)
    logos.check(target)
    original_path = tmp_path / "original.logos"
    original_receipt = logos.export_proof(target, original_path)
    original = json.loads(original_receipt.artifact)
    assert original["proof"] == {"tag": "theorem_ref", "id": "L"}
    assert original["lemmas"][0]["proof"]["proof"] == {"tag": "axiom_ref", "id": "A"}
    assert original["custom_axioms"][0]["id"] == "A"
    assert len(invocations) == 2
    valid = axiom.statement if change == "axiom-statement" else lemma._evidence
    invalid_term = AndElimL(AxiomRef(axiom))
    if change == "axiom-statement":
        axiom.statement = p & p
    elif change == "lemma-attachment":
        lemma.proof(exact(invalid_term))
    else:
        lemma._evidence = invalid_term

    assert not target.certified
    assert target.receipt is None
    assert len(invocations) == 2
    with pytest.raises(logos.LogosProofError, match=r'lemma\["L"\].*proof conclusion mismatch'):
        logos.check(target)
    _, rejected, result = invocations[-1]
    assert len(invocations) == 3 and result.returncode == 1
    assert result.stdout == b""
    assert json.loads(result.stderr)["status"] == "error"
    changed = json.loads(rejected)
    assert changed["target"] == original["target"]
    assert changed["proof"] == original["proof"]
    expected = json.loads(original_receipt.artifact)
    if change == "axiom-statement":
        expected["custom_axioms"][0]["statement"]["right"] = {"tag": "symbol", "id": "p2"}
    else:
        expected["lemmas"][0]["proof"]["tag"] = "and_elim_l"
    assert changed == expected
    assert not target.certified
    assert original_path.read_bytes() == original_receipt.artifact

    if change == "axiom-statement":
        axiom.statement = valid
    elif change == "lemma-attachment":
        lemma.proof(exact(valid))
    else:
        lemma._evidence = valid
    assert not target.certified
    logos.check(target)
    assert len(invocations) == 4 and invocations[-1][2].returncode == 0
    assert target.certified
    assert target.receipt is not original_receipt
    assert target.receipt.artifact == original_receipt.artifact == invocations[-1][1]
    assert target.receipt.artifact_sha256 == original_receipt.artifact_sha256


def test_apply_accepts_an_axiom_and_automatic_proof_accepts_a_lemma_hint(invocations):
    _, q, axiom, lemma, target = dependency_bundle()
    axiom.certified = True  # Author flags cannot certify anything.
    direct = logos.prove(axiom.statement, [apply(axiom)])
    logos.check(direct)
    assert json.loads(direct.receipt.artifact)["proof"] == {"tag": "axiom_ref", "id": "A"}
    assert not lemma.certified
    assert logos.prove(target, hints=[lemma]).certified
    assert not lemma.certified  # Target check validates reachable lemma evidence, not the lemma object.
    assert json.loads(invocations[-1][2].stdout)["custom_axioms"][0]["id"] == "A"
    assert json.loads(target.receipt.artifact)["target"] == {"tag": "symbol", "id": "p1"}

    pair = logos.prove(q & q, [split(), [apply(lemma)], [apply(lemma)]])
    logos.check(pair)
    bundle = json.loads(pair.receipt.artifact)
    assert len(bundle["lemmas"]) == len(bundle["custom_axioms"]) == 1
    assert bundle["proof"]["left"] == bundle["proof"]["right"] == {"tag": "theorem_ref", "id": "L"}
    assert len(json.loads(invocations[-1][2].stdout)["custom_axioms"]) == 1


def test_missing_lemma_proof_cannot_become_an_assumption(invocations):
    _, q, _, lemma, _ = dependency_bundle()
    missing = logos.Theorem(q, name="missing")
    missing.__dict__["certified"] = True
    target = logos.prove(q, [apply(missing)])
    with pytest.raises(logos.LogosProofError, match="has no proof attached"):
        logos.check(target)
    with pytest.raises(logos.LogosProofError, match="unsupported portable proof term AxiomRef"):
        logos.check(logos.prove(q, [exact(AxiomRef(missing))]))
    assert not invocations
    assert not target.certified

    lemma.proof(apply(lemma))
    with pytest.raises(logos.LogosProofError, match="cyclic theorem dependency"):
        logos.check(logos.prove(q, [apply(lemma)]))
    assert invocations[-1][2].returncode == 1


def test_conflicting_dependency_ids_are_rejected(invocations):
    _, _, axiom, lemma, target = dependency_bundle()
    axiom.name = lemma.name
    with pytest.raises(logos.LogosProofError, match="duplicate portable ID 'L'"):
        logos.check(target)
    assert not invocations
    assert not target.certified


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


def test_installed_case_tactics_discharge_both_disjuncts(invocations):
    p, q = logos.vars("P Q", bool)
    proof = logos.prove((p | q) >> (q | p), [
        intro("sum"), cases("sum", "branch"),
        [right(q), assumption()], [left(p), assumption()],
    ])
    assert logos.check(proof).certified
    bundle = json.loads(invocations[-1][1])
    split_term = bundle["proof"]["body"]
    assert split_term["tag"] == "or_elim"
    assert split_term["left"]["tag"] == "or_intro_r"
    assert split_term["right"]["tag"] == "or_intro_l"


def test_installed_negation_and_forward_implication_tactics(invocations):
    p, q, r = logos.vars("P Q R", bool)
    negated = logos.prove((p >> ~q) >> (p >> ~q), [
        intro("refute", "p", "q"), contradiction(),
    ])
    assert logos.check(negated).certified
    body = json.loads(invocations[-1][1])["proof"]["body"]["body"]
    assert body["tag"] == "not_intro"
    assert body["proof"]["body"]["tag"] == "not_elim"
    assert body["proof"]["body"]["negation"]["tag"] == "implies_elim"

    forward = logos.prove(logos.chain(p >> q, p, q), [
        intro("impl", "p"), have("q", "impl", "p"), assumption(),
    ])
    assert logos.check(forward).certified

    explosive = logos.prove(logos.chain(~(p & q), p, q, r), [
        intro("not_both", "p", "q"), contradiction(),
    ])
    assert logos.check(explosive).certified
    body = json.loads(invocations[-1][1])["proof"]["body"]["body"]["body"]
    assert body["tag"] == "ex_falso"
    assert body["proof"]["premise"]["tag"] == "and_intro"

    absurd = logos.prove(logos.lit(False) >> p, [intro("absurd"), contradiction()])
    assert logos.check(absurd).certified


@pytest.mark.parametrize("mistake,diagnostic", [
    ("leak", "out-of-scope hypothesis"),
    ("missing-case", "out-of-scope hypothesis"),
    ("case-mismatch", "case branches prove different conclusions"),
    ("case-source", "or_elim requires a disjunction"),
    ("not-intro", "not_intro requires an implication to falsehood"),
    ("not-elim", "negation operand does not match premise"),
    ("ex-falso", "ex_falso requires a proof of falsehood"),
    ("missing-falsehood", "out-of-scope hypothesis"),
    ("implication", "implication antecedent does not match premise"),
    ("or-sort", "has sort int, expected prop"),
])
def test_installed_checker_rejects_bogus_logic_evidence(mistake, diagnostic, invocations):
    p, q = logos.vars("P Q", bool)
    branch = HypRef("branch")
    flip_cases = CaseAnalysis(
        HypRef("sum"), "branch", OrIntroR(q, branch), OrIntroL(branch, p),
    )
    bad = {
        "leak": ((q | p) & p, AndIntro(flip_cases, branch)),
        "missing-case": (q | p, CaseAnalysis(HypRef("sum"), "branch", branch, HypRef("missing"))),
        "case-mismatch": (p, CaseAnalysis(HypRef("sum"), "branch", branch, branch)),
        "case-source": (p, CaseAnalysis(HypRef("p"), "branch", branch, branch)),
        "not-intro": (~p, NotIntro(ImpliesIntro(p, "h", HypRef("h")))),
        "not-elim": (logos.lit(False), NotElim(HypRef("not_p"), HypRef("q"))),
        "ex-falso": (q, ExFalso(HypRef("not_p"), q)),
        "missing-falsehood": (q, ExFalso(HypRef("missing"), q)),
        "implication": (p, ImpliesElim(ImpliesIntro(p, "h", HypRef("h")), HypRef("q"))),
        "or-sort": (p | q, OrIntroL(HypRef("p"), logos.lit(0))),
    }
    conclusion, term = bad[mistake]
    with pytest.raises(logos.LogosProofError, match=diagnostic):
        logos.check(logos.prove(logos.chain(p | q, p, q, ~p, conclusion), [
            intro("sum", "p", "q", "not_p"), exact(term),
        ]))
    assert invocations[-1][2].returncode == 1
    assert not invocations[-1][2].stdout
