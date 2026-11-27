use logos_checker::verify;
use serde_json::{Value, json};

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

/// A `have` whose binder the body ignores still appears in the trace, because
/// the Markdown reading names the discharged hypothesis.
#[test]
fn keeps_an_unused_have_assumption_in_the_trace() {
    let bound = json!({"tag": "bound", "index": 0});
    let equality = json!({"tag": "eq", "left": bound.clone(), "right": bound.clone()});
    let target = json!({"tag": "forall", "name": "x", "sort": "int", "body":
        {"tag": "implies", "left": equality.clone(), "right": equality.clone()}});
    let proof = json!({"tag": "forall_intro", "name": "x", "sort": "int", "body":
        {"tag": "implies_intro", "binder": "h", "premise": equality.clone(), "body":
        {"tag": "have", "binder": "unused", "statement": equality.clone(),
            "proof": {"tag": "refl", "term": bound.clone()},
            "body": {"tag": "refl", "term": bound.clone()}}}});
    let checked = verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
    let ids: std::collections::HashSet<&str> =
        checked.steps.iter().map(|step| step.id.as_str()).collect();
    for step in &checked.steps {
        for link in step
            .discharged
            .iter()
            .chain(step.discharged_cases.iter().flatten())
        {
            assert!(ids.contains(link.as_str()), "{} names {link}", step.id);
        }
    }
    assert!(checked
        .steps
        .iter()
        .any(|step| step.rule == "local_assumption" && step.binder.as_deref() == Some("unused")));
}
