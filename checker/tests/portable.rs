use logos_checker::verify;
use serde_json::{Value, json};
use std::process::Command;

const GOOD: &[u8] = include_bytes!("fixtures/portable/authorization.logos");
const WRONG: &[u8] = include_bytes!("fixtures/portable/wrong-projection.logos");
const TARGET: &str = "(Authenticated ∧ Authorized) → Authorized";

fn fixture(name: &str) -> String {
    format!(
        "{}/tests/fixtures/portable/{name}.logos",
        env!("CARGO_MANIFEST_DIR")
    )
}

#[test]
fn derives_the_statement_and_records_discharged_scope() {
    let checked = verify(GOOD).unwrap_or_else(|error| panic!("{error}"));
    assert_eq!(checked.judgment.statement_text, TARGET);
    assert_eq!(checked.judgment.theory, "logos-core-v1");
    assert!(checked.judgment.custom_axioms.is_empty());

    let [assumption, reference, projection, introduction] = checked.steps.as_slice() else {
        panic!("expected four checked steps");
    };
    assert_eq!(assumption.id, "proof.assumption");
    assert_eq!(assumption.rule, "local_assumption");
    assert_eq!(assumption.conclusion_text, "Authenticated ∧ Authorized");
    assert_eq!(reference.rule, "hyp_ref");
    assert_eq!(reference.premises, std::slice::from_ref(&assumption.id));
    assert_eq!(projection.rule, "and_elim_r");
    assert_eq!(projection.conclusion_text, "Authorized");
    assert_eq!(projection.premises, std::slice::from_ref(&reference.id));
    assert_eq!(introduction.rule, "implies_intro");
    assert_eq!(
        introduction.premises,
        [assumption.id.clone(), projection.id.clone()]
    );
    assert_eq!(
        introduction.discharged.as_deref(),
        Some(assumption.id.as_str())
    );
    assert_eq!(introduction.conclusion, checked.judgment.statement);
}

#[test]
fn rule_swap_is_a_checked_conclusion_mismatch() {
    let mut altered: Value = serde_json::from_slice(GOOD).unwrap();
    altered["proof"]["body"]["tag"] = json!("and_elim_l");
    assert_eq!(altered, serde_json::from_slice::<Value>(WRONG).unwrap());

    let output = Command::new(env!("CARGO_BIN_EXE_logos"))
        .args(["inspect", "--json", &fixture("wrong-projection")])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let diagnostic: Value = serde_json::from_slice(&output.stderr).unwrap();
    assert_eq!(diagnostic["status"], "error");
    let error = diagnostic["error"].as_str().unwrap();
    assert!(error.contains(&format!("Expected: {TARGET}")));
    assert!(error.contains("Derived:  (Authenticated ∧ Authorized) → Authenticated"));

    altered["target"]["right"] = json!({"tag": "symbol", "id": "p1"});
    let checked = verify(&serde_json::to_vec(&altered).unwrap()).ok().unwrap();
    assert_eq!(checked.steps[2].rule, "and_elim_l");
}

#[test]
fn checks_scope_and_rejects_malformed_inputs() {
    for (name, expected) in [
        ("out-of-scope", "out-of-scope hypothesis"),
        ("unsupported-version", "unsupported proof format"),
        ("duplicate-declaration", "duplicate declaration ID"),
        ("malformed-conjunction", "malformed proof file"),
        ("wrong-sort", "has sort int, expected prop"),
    ] {
        let bytes = std::fs::read(fixture(name)).unwrap();
        let error = verify(&bytes).err().unwrap();
        assert!(error.contains(expected), "{name}: {error}");
    }

    let original: Value = serde_json::from_slice(GOOD).unwrap();
    for (field, value, expected) in [
        ("theory", json!("unknown-theory"), "unsupported theory"),
        ("custom_axioms", json!([{}]), "dependencies are unsupported"),
        ("lemmas", json!([{}]), "dependencies are unsupported"),
        ("declarations", json!([]), "undeclared symbol"),
        (
            "proof",
            json!({"tag": "axiom", "id": "h"}),
            "unknown variant",
        ),
        ("verified", json!(true), "unknown field"),
    ] {
        let mut altered = original.clone();
        altered[field] = value;
        let error = verify(&serde_json::to_vec(&altered).unwrap())
            .err()
            .unwrap();
        assert!(error.contains(expected), "{field}: {error}");
    }
}

#[test]
fn a_shadowed_binder_resolves_to_its_nearest_scope() {
    let a = json!({"tag":"symbol","id":"p1"});
    let b = json!({"tag":"symbol","id":"p2"});
    let mut bundle: Value = serde_json::from_slice(GOOD).unwrap();
    bundle["target"] = json!({"tag":"implies","left":a,
        "right":{"tag":"implies","left":b,"right":b}});
    bundle["proof"] = json!({"tag":"implies_intro","binder":"h","premise":a,
        "body":{"tag":"implies_intro","binder":"h","premise":b,
            "body":{"tag":"hyp_ref","binder":"h"}}});
    let verified = verify(&serde_json::to_vec(&bundle).unwrap()).ok().unwrap();
    assert_eq!(verified.steps[2].premises, ["proof.body.assumption"]);
}

#[test]
fn json_preserves_declaration_identity_with_shared_labels() {
    let output = Command::new(env!("CARGO_BIN_EXE_logos"))
        .args([
            "check",
            "--json",
            "--deny-custom-axioms",
            &fixture("shared-label"),
        ])
        .output()
        .unwrap();
    assert!(output.status.success());
    let checked: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(
        checked["declarations"],
        json!([
            {"id":"p1","name":"Permission","sort":"prop"},
            {"id":"p2","name":"Permission","sort":"prop"},
        ])
    );
    assert_eq!(checked["statement"]["left"]["left"]["id"], "p1");
    assert_eq!(checked["statement"]["right"]["id"], "p2");
    assert_eq!(checked["custom_axioms"], json!([]));
    assert_eq!(checked["status"], "verified");
}
