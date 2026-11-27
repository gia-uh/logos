#![recursion_limit = "256"]
use logos_checker::verify;
use serde_json::{Value, json};

fn symbol(id: &str) -> Value {
    json!({"tag": "symbol", "id": id})
}

fn bound(index: usize) -> Value {
    json!({"tag": "bound", "index": index})
}

fn int(value: &str) -> Value {
    json!({"tag": "int", "value": value})
}

fn eq(left: Value, right: Value) -> Value {
    json!({"tag": "eq", "left": left, "right": right})
}

fn add(left: Value, right: Value) -> Value {
    json!({"tag": "add", "left": left, "right": right})
}

fn program_bundle(assign_value: Value) -> Vec<u8> {
    serde_json::to_vec(&json!({
        "format": "logos-proof-v1",
        "theory": "logos-core-v1",
        "name": null,
        "declarations": [
            {"id": "p1", "name": "x", "sort": "int"},
            {"id": "p2", "name": "y", "sort": "int"},
            {"id": "p3", "name": "result", "sort": "int"}
        ],
        "functions": [{
            "id": "f1", "name": "f", "params": ["int"], "result": "int"
        }],
        "programs": [{
            "id": "g1", "function": "f1",
            "params": ["p1"], "locals": ["p2"], "ghosts": [], "result": "p3",
            "requires": eq(symbol("p1"), symbol("p1")),
            "ensures": eq(symbol("p3"), symbol("p1")),
            "body": [
                {"tag": "assign", "name": "p2", "value": assign_value},
                {"tag": "return", "value": symbol("p2")}
            ],
            "obligations": [{
                "id": "main",
                "proof": {
                    "tag": "forall_intro", "name": "x", "sort": "int", "body":
                    {"tag": "forall_intro", "name": "y", "sort": "int", "body":
                    {"tag": "forall_intro", "name": "result", "sort": "int", "body":
                    {"tag": "implies_intro", "binder": "pre", "premise": eq(bound(2), bound(2)),
                        "body": {"tag": "core_law", "id": "add_zero", "args": [bound(2)]}}}}
                }
            }]
        }],
        "custom_axioms": [],
        "lemmas": [],
        "target": {
            "tag": "forall", "name": "x", "sort": "int", "body":
            {"tag": "forall", "name": "result", "sort": "int", "body":
            {"tag": "implies", "left": eq(bound(1), bound(1)),
                "right": {"tag": "implies",
                    "left": eq(bound(0), json!({"tag": "app", "id": "f1", "args": [bound(1)]})),
                    "right": eq(bound(0), bound(1))}}}
        },
        "proof": {"tag": "program_ref", "id": "g1"}
    }))
    .unwrap()
}

#[test]
fn verifies_a_straight_line_program_against_its_contract() {
    let checked = verify(&program_bundle(add(symbol("p1"), int("0"))))
        .unwrap_or_else(|error| panic!("{error}"));
    assert!(checked.judgment.custom_axioms.is_empty());
    assert!(checked.steps.iter().any(|step| step.rule == "program_ref"));
}

#[test]
fn rejects_a_mutated_program_body() {
    let error = verify(&program_bundle(add(symbol("p1"), int("1"))))
        .err()
        .unwrap();
    assert!(
        error.contains("proof conclusion mismatch") || error.contains("not contradictory"),
        "{error}"
    );
}

#[test]
fn rejects_a_missing_obligation() {
    let mut bundle: Value =
        serde_json::from_slice(&program_bundle(add(symbol("p1"), int("0")))).unwrap();
    bundle["programs"][0]["obligations"] = json!([]);
    let error = verify(&serde_json::to_vec(&bundle).unwrap()).err().unwrap();
    assert!(error.contains("missing proof"), "{error}");
}
