use logos_checker::verify;
use serde_json::{Value, json};

fn call(id: &str, callee: &str) -> Value {
    json!({
        "id": id,
        "callee": callee,
        "line": 1,
        "requires": {"tag": "int", "value": "0"},
        "ensures": {"tag": "int", "value": "0"}
    })
}

fn program(id: &str, function: &str, result: &str, calls: Vec<Value>) -> Value {
    json!({
        "id": id,
        "function": function,
        "params": [],
        "locals": [],
        "result": result,
        "requires": {"tag": "int", "value": "0"},
        "ensures": {"tag": "int", "value": "0"},
        "body": [],
        "calls": calls
    })
}

fn bundle(programs: Vec<Value>) -> Vec<u8> {
    serde_json::to_vec(&json!({
        "format": "logos-proof-v1",
        "theory": "logos-core-v1",
        "declarations": [],
        "functions": [
            {"id": "f1", "name": "f1", "params": [], "result": "int"},
            {"id": "f2", "name": "f2", "params": [], "result": "int"}
        ],
        "programs": programs,
        "custom_axioms": [],
        "lemmas": [],
        "target": {"tag": "int", "value": "0"},
        "proof": {"tag": "refl", "term": {"tag": "int", "value": "0"}}
    }))
    .unwrap()
}

fn error(bytes: &[u8]) -> String {
    match verify(bytes) {
        Ok(_) => panic!("expected a rejection"),
        Err(error) => error,
    }
}

#[test]
fn rejects_a_call_cycle_before_any_proof_is_used() {
    let programs = vec![
        program("g1", "f1", "r1", vec![call("c1", "g2")]),
        program("g2", "f2", "r2", vec![call("c2", "g1")]),
    ];
    let error = error(&bundle(programs));
    assert!(error.contains("cyclic call dependency"), "{error}");
}

#[test]
fn rejects_a_direct_self_call() {
    let programs = vec![program("g1", "f1", "r1", vec![call("c1", "g1")])];
    let error = error(&bundle(programs));
    assert!(error.contains("calls itself"), "{error}");
}

#[test]
fn rejects_an_unknown_callee_program() {
    let programs = vec![program("g1", "f1", "r1", vec![call("c1", "g9")])];
    let error = error(&bundle(programs));
    assert!(error.contains("unknown callee program"), "{error}");
}
