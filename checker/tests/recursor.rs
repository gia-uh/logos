use logos_checker::verify;
use serde_json::{Value, json};

fn bound(index: usize) -> Value {
    json!({"tag": "bound", "index": index})
}

fn int(value: i64) -> Value {
    json!({"tag": "int", "value": value.to_string()})
}

fn eq(left: Value, right: Value) -> Value {
    json!({"tag": "eq", "left": left, "right": right})
}

fn add(left: Value, right: Value) -> Value {
    json!({"tag": "add", "left": left, "right": right})
}

fn mul(left: Value, right: Value) -> Value {
    json!({"tag": "mul", "left": left, "right": right})
}

fn app(id: &str, args: Vec<Value>) -> Value {
    json!({"tag": "app", "id": id, "args": args})
}

fn factorial_like(id: &str) -> Value {
    // f(0) = 1; f(n + 1) = (n + 1) * f(n)
    json!({
        "id": id, "name": "factorial_like", "params": ["int"], "result": "int",
        "recursor": {
            "base": int(1),
            "step": mul(add(bound(1), int(1)), bound(0))
        }
    })
}

fn bundle(functions: Vec<Value>, target: Value, proof: Value) -> Vec<u8> {
    serde_json::to_vec(&json!({
        "format": "logos-proof-v1",
        "theory": "logos-core-v1",
        "name": null,
        "declarations": [],
        "functions": functions,
        "custom_axioms": [],
        "lemmas": [],
        "target": target,
        "proof": proof,
    }))
    .unwrap()
}

#[test]
fn applies_the_base_equation() {
    let artifact = bundle(
        vec![factorial_like("f1")],
        eq(app("f1", vec![int(0)]), int(1)),
        json!({"tag": "recursor_base", "id": "f1"}),
    );
    let checked = verify(&artifact).unwrap_or_else(|error| panic!("{error}"));
    assert!(checked.judgment.custom_axioms.is_empty());
    assert!(
        checked
            .steps
            .iter()
            .any(|step| step.rule == "recursor_base")
    );
}

#[test]
fn applies_the_step_equation_at_a_nonnegative_argument() {
    let artifact = bundle(
        vec![factorial_like("f1")],
        eq(
            app("f1", vec![int(1)]),
            mul(int(1), app("f1", vec![int(0)])),
        ),
        json!({"tag": "recursor_step", "id": "f1", "argument": int(0),
            "proof": {"tag": "core_law", "id": "lt_irrefl", "args": [int(0)]}}),
    );
    let checked = verify(&artifact).unwrap_or_else(|error| panic!("{error}"));
    assert!(
        checked
            .steps
            .iter()
            .any(|step| step.rule == "recursor_step")
    );
}

#[test]
fn rejects_a_recursive_call_away_from_the_predecessor() {
    let mut function = factorial_like("f1");
    function["recursor"]["step"] = mul(
        add(bound(1), int(1)),
        app("f1", vec![add(bound(1), int(1))]),
    );
    let artifact = bundle(
        vec![function],
        eq(app("f1", vec![int(0)]), int(1)),
        json!({"tag": "recursor_base", "id": "f1"}),
    );
    let error = verify(&artifact).err().unwrap();
    assert!(error.contains("away from its predecessor"), "{error}");
}

#[test]
fn rejects_a_step_without_a_nonnegative_argument() {
    let artifact = bundle(
        vec![factorial_like("f1")],
        eq(
            app("f1", vec![int(1)]),
            mul(int(1), app("f1", vec![int(0)])),
        ),
        json!({"tag": "recursor_step", "id": "f1", "argument": int(0),
            "proof": {"tag": "refl", "term": int(0)}}),
    );
    let error = verify(&artifact).err().unwrap();
    assert!(error.contains("nonnegative argument"), "{error}");
}

#[test]
fn rejects_a_function_with_both_a_body_and_a_recursor() {
    let mut function = factorial_like("f1");
    function["body"] = int(1);
    let artifact = bundle(
        vec![function],
        eq(app("f1", vec![int(0)]), int(1)),
        json!({"tag": "recursor_base", "id": "f1"}),
    );
    let error = verify(&artifact).err().unwrap();
    assert!(error.contains("both a body and a recursor"), "{error}");
}

#[test]
fn rejects_a_recursor_base_on_an_opaque_function() {
    let artifact = bundle(
        vec![json!({"id": "f1", "name": "opaque", "params": ["int"], "result": "int"})],
        eq(app("f1", vec![int(0)]), int(1)),
        json!({"tag": "recursor_base", "id": "f1"}),
    );
    let error = verify(&artifact).err().unwrap();
    assert!(error.contains("not a recursive definition"), "{error}");
}

#[test]
fn rejects_a_recursor_with_a_non_integer_step() {
    let mut function = factorial_like("f1");
    function["recursor"]["step"] = json!({"tag": "eq", "left": bound(1), "right": bound(0)});
    let artifact = bundle(
        vec![function],
        eq(app("f1", vec![int(0)]), int(1)),
        json!({"tag": "recursor_base", "id": "f1"}),
    );
    let error = verify(&artifact).err().unwrap();
    assert!(error.contains("has sort prop, expected int"), "{error}");
}
