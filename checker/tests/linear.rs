use logos_checker::verify;
use serde_json::{Value, json};

fn bound(index: usize) -> Value {
    json!({"tag": "bound", "index": index})
}

fn le(left: Value, right: Value) -> Value {
    json!({"tag": "le", "left": left, "right": right})
}

fn lt(left: Value, right: Value) -> Value {
    json!({"tag": "lt", "left": left, "right": right})
}

fn add(left: Value, right: Value) -> Value {
    json!({"tag": "add", "left": left, "right": right})
}

fn int(value: &str) -> Value {
    json!({"tag": "int", "value": value})
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

#[test]
fn closes_a_linear_successor_goal() {
    let target = json!({
        "tag": "forall", "name": "x", "sort": "int", "body":
        {"tag": "implies", "left": le(int("0"), bound(0)),
            "right": lt(bound(0), add(bound(0), int("1")))}
    });
    let proof = json!({
        "tag": "forall_intro", "name": "x", "sort": "int", "body":
        {"tag": "implies_intro", "binder": "h", "premise": le(int("0"), bound(0)),
            "body": {"tag": "linear",
                "conclusion": lt(bound(0), add(bound(0), int("1"))),
                "terms": []}}
    });
    let checked = verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
    assert!(checked.judgment.custom_axioms.is_empty());
    assert!(checked.steps.iter().any(|step| step.rule == "linear"));
}

#[test]
fn uses_a_non_negative_hypothesis_coefficient() {
    let target = json!({
        "tag": "forall", "name": "a", "sort": "int", "body":
        {"tag": "forall", "name": "b", "sort": "int", "body":
        {"tag": "implies", "left": le(bound(1), bound(0)),
            "right": le(add(bound(1), int("1")), add(bound(0), int("1")))}}
    });
    let proof = json!({
        "tag": "forall_intro", "name": "a", "sort": "int", "body":
        {"tag": "forall_intro", "name": "b", "sort": "int", "body":
        {"tag": "implies_intro", "binder": "h", "premise": le(bound(1), bound(0)),
            "body": {"tag": "linear",
                "conclusion": le(add(bound(1), int("1")), add(bound(0), int("1"))),
                "terms": [{"binder": "h", "coefficient": "1"}]}}}
    });
    verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
}

#[test]
fn rejects_a_negative_inequality_coefficient() {
    let target = json!({
        "tag": "forall", "name": "a", "sort": "int", "body":
        {"tag": "forall", "name": "b", "sort": "int", "body":
        {"tag": "implies", "left": le(bound(1), bound(0)),
            "right": le(add(bound(1), int("1")), add(bound(0), int("1")))}}
    });
    let proof = json!({
        "tag": "forall_intro", "name": "a", "sort": "int", "body":
        {"tag": "forall_intro", "name": "b", "sort": "int", "body":
        {"tag": "implies_intro", "binder": "h", "premise": le(bound(1), bound(0)),
            "body": {"tag": "linear",
                "conclusion": le(add(bound(1), int("1")), add(bound(0), int("1"))),
                "terms": [{"binder": "h", "coefficient": "-1"}]}}}
    });
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(error.contains("non-negative coefficient"), "{error}");
}

#[test]
fn rejects_a_non_contradictory_combination() {
    let target = json!({
        "tag": "forall", "name": "a", "sort": "int", "body":
        {"tag": "forall", "name": "b", "sort": "int", "body":
        {"tag": "implies", "left": le(bound(1), bound(0)),
            "right": le(bound(0), bound(1))}}
    });
    let proof = json!({
        "tag": "forall_intro", "name": "a", "sort": "int", "body":
        {"tag": "forall_intro", "name": "b", "sort": "int", "body":
        {"tag": "implies_intro", "binder": "h", "premise": le(bound(1), bound(0)),
            "body": {"tag": "linear",
                "conclusion": le(bound(0), bound(1)),
                "terms": [{"binder": "h", "coefficient": "1"}]}}}
    });
    // The conclusion is already a hypothesis, so a linear certificate is not
    // contradictory; the checker must reject it even though the theorem is true.
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(error.contains("not contradictory"), "{error}");
}
