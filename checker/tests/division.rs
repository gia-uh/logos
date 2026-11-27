//! Floor-division and non-negative product laws used by production contracts.
use logos_checker::verify;
use serde_json::{Value, json};

fn bound(index: usize) -> Value {
    json!({"tag": "bound", "index": index})
}

fn int(value: i64) -> Value {
    json!({"tag": "int", "value": value.to_string()})
}

fn lt(left: Value, right: Value) -> Value {
    json!({"tag": "lt", "left": left, "right": right})
}

fn le(left: Value, right: Value) -> Value {
    json!({"tag": "le", "left": left, "right": right})
}

fn div(left: Value, right: Value) -> Value {
    json!({"tag": "div", "left": left, "right": right})
}

fn mul(left: Value, right: Value) -> Value {
    json!({"tag": "mul", "left": left, "right": right})
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

fn two_binders(body: Value) -> Value {
    json!({
        "tag": "forall", "name": "a", "sort": "int", "body":
        {"tag": "forall", "name": "b", "sort": "int", "body": body}
    })
}

fn prove_two_binders(conclusion: Value, law: &str, extra: &str) -> (Value, Value) {
    let premise_one = if extra == "strict" {
        lt(int(0), bound(1))
    } else {
        le(int(0), bound(1))
    };
    let premise_two = if law == "div_lt" {
        lt(int(1), bound(0))
    } else if law == "div_nonneg" {
        lt(int(0), bound(0))
    } else {
        le(int(0), bound(0))
    };
    let target = two_binders(json!({
        "tag": "implies", "left": premise_one.clone(), "right":
        {"tag": "implies", "left": premise_two.clone(), "right": conclusion}
    }));
    let first = json!({
        "tag": "implies_elim",
        "implication": {"tag": "core_law", "id": law,
            "args": [bound(1), bound(0)]},
        "premise": {"tag": "hyp_ref", "binder": "h1"}
    });
    let second = json!({
        "tag": "implies_elim",
        "implication": first,
        "premise": {"tag": "hyp_ref", "binder": "h2"}
    });
    let proof = json!({
        "tag": "forall_intro", "name": "a", "sort": "int", "body":
        {"tag": "forall_intro", "name": "b", "sort": "int", "body":
        {"tag": "implies_intro", "binder": "h1", "premise": premise_one, "body":
        {"tag": "implies_intro", "binder": "h2", "premise": premise_two, "body": second}}}
    });
    (target, proof)
}

#[test]
fn division_by_a_positive_divisor_is_non_negative() {
    let (target, proof) = prove_two_binders(
        le(int(0), div(bound(1), bound(0))),
        "div_nonneg",
        "nonstrict",
    );
    let checked = verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
    assert!(checked.judgment.custom_axioms.is_empty());
    assert!(
        checked
            .steps
            .iter()
            .any(|step| step.reference_id.as_deref() == Some("div_nonneg"))
    );
}

#[test]
fn division_by_a_divisor_above_one_decreases() {
    let (target, proof) =
        prove_two_binders(lt(div(bound(1), bound(0)), bound(1)), "div_lt", "strict");
    let checked = verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
    assert!(checked.judgment.custom_axioms.is_empty());
    assert!(
        checked
            .steps
            .iter()
            .any(|step| step.reference_id.as_deref() == Some("div_lt"))
    );
}

#[test]
fn a_product_of_non_negative_integers_is_non_negative() {
    let (target, proof) = prove_two_binders(
        le(int(0), mul(bound(1), bound(0))),
        "mul_nonneg",
        "nonstrict",
    );
    let checked = verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
    assert!(checked.judgment.custom_axioms.is_empty());
    assert!(
        checked
            .steps
            .iter()
            .any(|step| step.reference_id.as_deref() == Some("mul_nonneg"))
    );
}

#[test]
fn a_wrong_law_arity_is_rejected() {
    let (target, mut proof) = prove_two_binders(
        le(int(0), div(bound(1), bound(0))),
        "div_nonneg",
        "nonstrict",
    );
    proof["body"]["body"]["body"]["body"]["implication"]["implication"]["args"] = json!([bound(1)]);
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(error.contains("requires 2 substitutions"), "{error}");
}
