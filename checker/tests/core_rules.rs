use logos_checker::verify;
use serde_json::{Value, json};

fn bound(index: usize) -> Value {
    json!({"tag": "bound", "index": index})
}

fn eq(left: Value, right: Value) -> Value {
    json!({"tag": "eq", "left": left, "right": right})
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

/// forall a, forall c, (exists x, x = a) -> a = a
fn existential_elimination() -> (Value, Value) {
    let existential = json!({
        "tag": "exists", "name": "x", "sort": "int",
        "body": eq(bound(0), bound(2))
    });
    let target = json!({
        "tag": "forall", "name": "a", "sort": "int", "body":
        {"tag": "forall", "name": "c", "sort": "int", "body":
        {"tag": "implies", "left": existential.clone(), "right": eq(bound(1), bound(1))}}
    });
    let proof = json!({
        "tag": "forall_intro", "name": "a", "sort": "int", "body":
        {"tag": "forall_intro", "name": "c", "sort": "int", "body":
        {"tag": "implies_intro", "binder": "e", "premise": existential, "body":
        {"tag": "exists_elim", "proof": {"tag": "hyp_ref", "binder": "e"},
            "name": "x", "binder": "h",
            "body": {"tag": "refl", "term": bound(2)}}}}
    });
    (target, proof)
}

#[test]
fn eliminates_an_existential_with_a_fresh_witness() {
    let (target, proof) = existential_elimination();
    let checked = verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
    assert!(checked.judgment.custom_axioms.is_empty());
    let step = checked
        .steps
        .iter()
        .find(|step| step.rule == "exists_elim")
        .expect("checked existential elimination step");
    assert_eq!(step.binder.as_deref(), Some("x"));
    assert!(step.discharged.is_some());
}

#[test]
fn rejects_an_escaping_eigenvariable() {
    let (target, mut proof) = existential_elimination();
    proof["body"]["body"]["body"]["body"]["term"] = bound(0);
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(error.contains("eigenvariable escapes"), "{error}");
}

#[test]
fn rejects_eliminating_a_non_existential() {
    let (target, mut proof) = existential_elimination();
    proof["body"]["body"]["body"]["proof"] = json!({"tag": "refl", "term": bound(1)});
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(error.contains("requires an existential"), "{error}");
}

/// forall a, forall b, a = b -> b = b
fn equality_substitution() -> (Value, Value) {
    let target = json!({
        "tag": "forall", "name": "a", "sort": "int", "body":
        {"tag": "forall", "name": "b", "sort": "int", "body":
        {"tag": "implies", "left": eq(bound(1), bound(0)), "right": eq(bound(0), bound(0))}}
    });
    let proof = json!({
        "tag": "forall_intro", "name": "a", "sort": "int", "body":
        {"tag": "forall_intro", "name": "b", "sort": "int", "body":
        {"tag": "implies_intro", "binder": "h", "premise": eq(bound(1), bound(0)), "body":
        {"tag": "eq_subst", "equality": {"tag": "hyp_ref", "binder": "h"},
            "context": eq(bound(0), bound(0)),
            "proof": {"tag": "refl", "term": bound(1)}}}}
    });
    (target, proof)
}

#[test]
fn substitutes_an_equality_inside_a_proposition() {
    let (target, proof) = equality_substitution();
    let checked = verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
    assert!(checked.judgment.custom_axioms.is_empty());
    assert!(checked.steps.iter().any(|step| step.rule == "eq_subst"));
}

#[test]
fn rejects_a_premise_that_does_not_match_the_left_instance() {
    let (target, mut proof) = equality_substitution();
    proof["body"]["body"]["body"]["proof"]["term"] = bound(0);
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(error.contains("does not establish P(left)"), "{error}");
}

#[test]
fn rejects_a_non_proposition_template() {
    let (target, mut proof) = equality_substitution();
    proof["body"]["body"]["body"]["context"] = json!({"tag": "int", "value": "0"});
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(error.contains("has sort int, expected prop"), "{error}");
}
