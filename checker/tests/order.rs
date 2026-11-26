use logos_checker::verify;
use serde_json::{Value, json};

fn bound(index: usize) -> Value {
    json!({"tag": "bound", "index": index})
}

fn lt(left: Value, right: Value) -> Value {
    json!({"tag": "lt", "left": left, "right": right})
}

fn add(left: Value, right: Value) -> Value {
    json!({"tag": "add", "left": left, "right": right})
}

fn bundle(target: Value, proof: Value) -> Vec<u8> {
    serde_json::to_vec(&json!({
        "format": "logos-proof-v1",
        "theory": "logos-core-v1",
        "name": null,
        "declarations": [],
        "custom_axioms": [],
        "lemmas": [],
        "target": target,
        "proof": proof,
    }))
    .unwrap()
}

fn transport() -> (Value, Value) {
    let target = json!({
        "tag": "forall", "name": "a", "sort": "int", "body":
        {"tag": "forall", "name": "b", "sort": "int", "body":
        {"tag": "forall", "name": "c", "sort": "int", "body":
        {"tag": "implies",
            "left": lt(bound(2), bound(1)),
            "right": lt(add(bound(2), bound(0)), add(bound(1), bound(0)))}}}
    });
    let proof = json!({
        "tag": "forall_intro", "name": "a", "sort": "int", "body":
        {"tag": "forall_intro", "name": "b", "sort": "int", "body":
        {"tag": "forall_intro", "name": "c", "sort": "int", "body":
        {"tag": "implies_intro", "binder": "h",
            "premise": lt(bound(2), bound(1)),
            "body": {"tag": "implies_elim",
                "implication": {"tag": "core_law", "id": "lt_add",
                    "args": [bound(2), bound(1), bound(0)]},
                "premise": {"tag": "hyp_ref", "binder": "h"}}}}}
    });
    (target, proof)
}

#[test]
fn transports_a_strict_inequality_through_addition() {
    let (target, proof) = transport();
    let checked = verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
    assert!(checked.judgment.custom_axioms.is_empty());
    assert_eq!(checked.judgment.theory, "logos-core-v1");
    assert!(checked.judgment.statement_text.contains('<'));
    let law = checked
        .steps
        .iter()
        .find(|step| step.rule == "core_law")
        .expect("checked core law step");
    assert_eq!(law.reference_id.as_deref(), Some("lt_add"));
    assert_eq!(
        law.explanation,
        "Adding the same integer to both sides preserves a strict integer inequality."
    );
}

#[test]
fn derives_disequality_from_strict_order() {
    let target = json!({
        "tag": "forall", "name": "a", "sort": "int", "body":
        {"tag": "forall", "name": "b", "sort": "int", "body":
        {"tag": "implies",
            "left": lt(bound(1), bound(0)),
            "right": {"tag": "not", "operand":
                {"tag": "eq", "left": bound(1), "right": bound(0)}}}}
    });
    let proof = json!({
        "tag": "forall_intro", "name": "a", "sort": "int", "body":
        {"tag": "forall_intro", "name": "b", "sort": "int", "body":
        {"tag": "implies_intro", "binder": "h",
            "premise": lt(bound(1), bound(0)),
            "body": {"tag": "implies_elim",
                "implication": {"tag": "core_law", "id": "lt_neq",
                    "args": [bound(1), bound(0)]},
                "premise": {"tag": "hyp_ref", "binder": "h"}}}}
    });
    let checked = verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
    let law = checked
        .steps
        .iter()
        .find(|step| step.rule == "core_law")
        .expect("checked core law step");
    assert_eq!(law.reference_id.as_deref(), Some("lt_neq"));
}

#[test]
fn rejects_reversed_law_instances() {
    let (target, mut proof) = transport();
    proof["body"]["body"]["body"]["body"]["implication"]["args"] =
        json!([bound(1), bound(2), bound(0)]);
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(
        error.contains("antecedent does not match premise")
            || error.contains("proof conclusion mismatch"),
        "{error}"
    );
}

#[test]
fn rejects_a_forged_premise() {
    let (target, mut proof) = transport();
    proof["body"]["body"]["body"]["premise"] = lt(bound(1), bound(2));
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(
        error.contains("antecedent does not match premise")
            || error.contains("proof conclusion mismatch"),
        "{error}"
    );
}

#[test]
fn rejects_unknown_laws_and_wrong_arity() {
    let (target, mut proof) = transport();
    proof["body"]["body"]["body"]["body"]["implication"]["id"] = json!("lt_reverse");
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(error.contains("unknown core law"), "{error}");

    let (target, mut proof) = transport();
    proof["body"]["body"]["body"]["body"]["implication"]["args"] = json!([bound(2), bound(1)]);
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(error.contains("requires 3 substitutions"), "{error}");
}

#[test]
fn rejects_non_integer_order_operands() {
    let bundle = serde_json::to_vec(&json!({
        "format": "logos-proof-v1",
        "theory": "logos-core-v1",
        "name": null,
        "declarations": [{"id": "p1", "name": "P", "sort": "prop"}],
        "custom_axioms": [],
        "lemmas": [],
        "target": lt(json!({"tag": "symbol", "id": "p1"}), json!({"tag": "int", "value": "0"})),
        "proof": {"tag": "refl", "term": {"tag": "int", "value": "0"}},
    }))
    .unwrap();
    let error = verify(&bundle).err().unwrap();
    assert!(error.contains("has sort prop, expected int"), "{error}");

    let bundle = serde_json::to_vec(&json!({
        "format": "logos-proof-v1",
        "theory": "logos-core-v1",
        "name": null,
        "declarations": [],
        "custom_axioms": [],
        "lemmas": [],
        "target": add(
            lt(json!({"tag": "int", "value": "0"}), json!({"tag": "int", "value": "1"})),
            json!({"tag": "int", "value": "1"})
        ),
        "proof": {"tag": "refl", "term": {"tag": "int", "value": "0"}},
    }))
    .unwrap();
    let error = verify(&bundle).err().unwrap();
    assert!(error.contains("has sort prop, expected int"), "{error}");
}

#[test]
fn proves_irreflexivity_and_transitivity() {
    let target = json!({
        "tag": "forall", "name": "a", "sort": "int", "body":
        {"tag": "not", "operand": lt(bound(0), bound(0))}
    });
    let proof = json!({
        "tag": "forall_intro", "name": "a", "sort": "int", "body":
        {"tag": "core_law", "id": "lt_irrefl", "args": [bound(0)]}
    });
    verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));

    let target = json!({
        "tag": "forall", "name": "a", "sort": "int", "body":
        {"tag": "forall", "name": "b", "sort": "int", "body":
        {"tag": "forall", "name": "c", "sort": "int", "body":
        {"tag": "implies",
            "left": lt(bound(2), bound(1)),
            "right": {"tag": "implies",
                "left": lt(bound(1), bound(0)),
                "right": lt(bound(2), bound(0))}}}}
    });
    let proof = json!({
        "tag": "forall_intro", "name": "a", "sort": "int", "body":
        {"tag": "forall_intro", "name": "b", "sort": "int", "body":
        {"tag": "forall_intro", "name": "c", "sort": "int", "body":
        {"tag": "implies_intro", "binder": "h1",
            "premise": lt(bound(2), bound(1)),
            "body": {"tag": "implies_intro", "binder": "h2",
                "premise": lt(bound(1), bound(0)),
                "body": {"tag": "implies_elim",
                    "implication": {"tag": "implies_elim",
                        "implication": {"tag": "core_law", "id": "lt_trans",
                            "args": [bound(2), bound(1), bound(0)]},
                        "premise": {"tag": "hyp_ref", "binder": "h1"}},
                    "premise": {"tag": "hyp_ref", "binder": "h2"}}}}}}
    });
    verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
}
