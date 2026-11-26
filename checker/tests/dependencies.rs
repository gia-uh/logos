use logos_checker::{Verified, verify};
use serde_json::{Value, json};
use std::{
    io::Write,
    process::{Command, Output, Stdio},
};

fn bundle() -> Value {
    serde_json::from_str(include_str!("fixtures/portable/dependencies.logos")).unwrap()
}

fn checked(value: &Value) -> Result<Verified, String> {
    verify(&serde_json::to_vec(value).unwrap())
}

fn cli(value: &Value, args: &[&str]) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_logos"))
        .args(args)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(&serde_json::to_vec(value).unwrap())
        .unwrap();
    child.wait_with_output().unwrap()
}

#[test]
fn follows_checked_lemmas_once_and_reports_only_used_axioms() {
    let mut value = bundle();
    // Check forward references and two uses of a lemma inside another lemma.
    let inner = value["lemmas"][0].clone();
    let q = value["target"].clone();
    let p = value["custom_axioms"][0]["statement"]["left"].clone();
    let pair = json!({"tag":"and", "left":q, "right":q});
    let use_l = value["proof"].clone();
    value["lemmas"] = json!([
        {"id":"Pair", "statement":pair, "proof":{"tag":"and_intro", "left":use_l, "right":use_l}},
        {"id":"UnusedLemma", "statement":p, "proof":{"tag":"axiom_ref", "id":"Unused"}},
        inner,
    ]);
    value["custom_axioms"]
        .as_array_mut()
        .unwrap()
        .push(json!({"id":"Unused","statement":p}));
    value["declarations"][1]["name"] = json!("Q");
    value["target"] = json!({"tag":"implies", "left":p, "right":pair});
    value["proof"] = json!({"tag":"implies_intro", "binder":"A", "premise":p,
        "body":{"tag":"theorem_ref","id":"Pair"}});

    let verified = checked(&value).ok().unwrap();
    assert_eq!(verified.judgment.custom_axioms.len(), 1);
    let assumption = &verified.judgment.custom_axioms[0];
    assert_eq!(assumption.id, "A");
    assert_eq!(
        assumption.statement,
        serde_json::from_value(value["custom_axioms"][0]["statement"].clone()).unwrap()
    );
    assert_eq!(assumption.statement_text, "Q[\"p2\"]:prop ∧ Q[\"p1\"]:prop");
    assert_eq!(
        assumption.path,
        [
            "proof",
            "proof.body",
            "lemma[\"Pair\"].proof",
            "lemma[\"Pair\"].proof.left",
            "lemma[\"L\"].proof",
            "lemma[\"L\"].proof.proof"
        ]
    );
    assert_eq!(
        verified
            .steps
            .iter()
            .filter(|step| step.reference_id.as_deref() == Some("L"))
            .count(),
        2
    );
    assert_eq!(
        verified
            .steps
            .iter()
            .filter(|step| step.rule == "axiom_ref")
            .count(),
        1
    );
    assert_eq!(
        verified.steps.last().unwrap().discharged.as_deref(),
        Some("proof.assumption")
    );
}

#[test]
fn rejects_bad_dependency_evidence_and_names() {
    let original = bundle();
    for (path, replacement, expected) in [
        (
            "/lemmas/0/statement/id",
            json!("p2"),
            "proof conclusion mismatch",
        ),
        ("/lemmas/0/proof", Value::Null, "malformed proof file"),
        ("/lemmas/0/id", json!("p1"), "duplicate lemma ID"),
        ("/custom_axioms/0/id", json!("L"), "duplicate lemma ID"),
        (
            "/custom_axioms/0/statement/right/id",
            json!("p2"),
            "proof conclusion mismatch",
        ),
        ("/declarations/1/sort", json!("int"), "expected prop"),
        (
            "/lemmas/0/proof/tag",
            json!("and_elim_l"),
            "proof conclusion mismatch",
        ),
        ("/proof/id", json!("A"), "unknown theorem reference"),
        (
            "/lemmas/0/proof/proof/id",
            json!("L"),
            "unknown axiom reference",
        ),
        (
            "/lemmas/0/proof",
            original["proof"].clone(),
            "cyclic theorem dependency",
        ),
        (
            "/lemmas/0/proof",
            json!({"tag":"theorem_ref","id":"missing"}),
            "unknown theorem reference",
        ),
        ("/custom_axioms", json!([]), "unknown axiom reference"),
        (
            "/lemmas",
            json!([original["lemmas"][0], original["lemmas"][0]]),
            "duplicate lemma ID",
        ),
        (
            "/custom_axioms",
            json!([original["custom_axioms"][0], original["custom_axioms"][0]]),
            "duplicate axiom ID",
        ),
    ] {
        let mut value = original.clone();
        *value.pointer_mut(path).unwrap() = replacement;
        let error = checked(&value).err().unwrap();
        assert!(error.contains(expected), "{path}: {error}");
    }
    let mut value = original.clone();
    value["lemmas"][0].as_object_mut().unwrap().remove("proof");
    assert!(
        checked(&value)
            .err()
            .unwrap()
            .contains("missing field `proof`")
    );

    let mut value = original.clone();
    value["lemmas"][0]["proof"] = json!({"tag":"theorem_ref", "id":"Other"});
    value["lemmas"]
        .as_array_mut()
        .unwrap()
        .push(json!({"id":"Other", "statement":original["target"], "proof":original["proof"]}));
    assert!(
        checked(&value)
            .err()
            .unwrap()
            .contains("cyclic theorem dependency")
    );

    let mut value = original.clone();
    value["target"] =
        json!({"tag":"implies", "left":original["target"], "right":original["target"]});
    value["proof"] = json!({"tag":"implies_intro", "binder":"h", "premise":original["target"], "body":original["proof"]});
    value["lemmas"][0]["proof"] = json!({"tag":"hyp_ref", "binder":"h"});
    assert!(
        checked(&value)
            .err()
            .unwrap()
            .contains("out-of-scope hypothesis")
    );
}

#[test]
fn strict_reports_the_checked_assumptions_and_never_masks_invalidity() {
    let mut value = bundle();
    for operation in ["check", "inspect"] {
        let output = cli(&value, &[operation, "--json"]);
        assert_eq!(output.status.code(), Some(0));
        let mut default: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(default["status"], "verified");
        assert_eq!(default["custom_axioms"][0]["id"], "A");
        if operation == "inspect" {
            assert_eq!(default["steps"][0]["reference_id"], "A");
            assert_eq!(default["steps"][2]["reference_id"], "L");
        }
        let output = cli(&value, &[operation, "--json", "--strict"]);
        assert_eq!(output.status.code(), Some(3));
        let result: Value = serde_json::from_slice(&output.stdout).unwrap();
        default["status"] = json!("policy_denied");
        assert_eq!(result, default);
    }
    let output = cli(&value, &["check", "--strict"]);
    let printed = String::from_utf8(output.stdout).unwrap();
    assert!(printed.contains("Policy denied"));
    assert!(printed.contains("P[\"p2\"]:prop ∧ Q[\"p1\"]:prop"));
    assert!(printed.contains("proof → lemma[\"L\"].proof → lemma[\"L\"].proof.proof"));
    value["lemmas"][0]["proof"]["tag"] = json!("and_elim_l");
    let output = cli(&value, &["inspect", "--strict", "--json"]);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let error: Value = serde_json::from_slice(&output.stderr).unwrap();
    assert_eq!(error["status"], "error");
    assert!(
        error["error"]
            .as_str()
            .unwrap()
            .contains("proof conclusion mismatch")
    );
}
