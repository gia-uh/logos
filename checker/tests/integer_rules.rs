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

fn lt(left: Value, right: Value) -> Value {
    json!({"tag": "lt", "left": left, "right": right})
}

fn not(operand: Value) -> Value {
    json!({"tag": "not", "operand": operand})
}

fn implies(left: Value, right: Value) -> Value {
    json!({"tag": "implies", "left": left, "right": right})
}

fn and(left: Value, right: Value) -> Value {
    json!({"tag": "and", "left": left, "right": right})
}

fn or(left: Value, right: Value) -> Value {
    json!({"tag": "or", "left": left, "right": right})
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

fn induction() -> (Value, Value) {
    let target = json!({
        "tag": "forall", "name": "n", "sort": "int", "body":
        implies(not(lt(bound(0), int(0))), eq(bound(0), bound(0)))
    });
    let proof = json!({
        "tag": "induction", "bound": int(0), "name": "n",
        "predicate": eq(bound(0), bound(0)),
        "base": {"tag": "refl", "term": int(0)},
        "step": {"tag": "forall_intro", "name": "k", "sort": "int", "body":
            {"tag": "implies_intro", "binder": "lower",
                "premise": not(lt(bound(0), int(0))), "body":
            {"tag": "implies_intro", "binder": "previous",
                "premise": eq(bound(0), bound(0)), "body":
            {"tag": "refl", "term": add(bound(0), int(1))}}}}
    });
    (target, proof)
}

#[test]
fn proves_a_property_by_integer_induction() {
    let (target, proof) = induction();
    let checked = verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
    assert!(checked.judgment.custom_axioms.is_empty());
    assert!(checked.steps.iter().any(|step| step.rule == "induction"));
}

#[test]
fn rejects_a_wrong_induction_base() {
    let (target, mut proof) = induction();
    proof["base"]["term"] = int(1);
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(error.contains("induction base"), "{error}");
}

#[test]
fn rejects_a_wrong_induction_step() {
    let (target, mut proof) = induction();
    proof["step"]["body"]["body"]["premise"] = eq(bound(0), int(0));
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(
        error.contains("induction step") || error.contains("antecedent"),
        "{error}"
    );
}

fn least() -> (Value, Value) {
    let membership = json!({
        "tag": "and",
        "left": not(lt(bound(0), int(5))),
        "right": eq(bound(0), int(5))
    });
    let target = json!({
        "tag": "exists", "name": "m", "sort": "int", "body":
        and(membership, json!({
            "tag": "forall", "name": "k", "sort": "int", "body":
            implies(
                and(not(lt(bound(0), int(5))), lt(bound(0), bound(1))),
                not(eq(bound(0), int(5)))
            )
        }))
    });
    let proof = json!({
        "tag": "least", "bound": int(5), "name": "m",
        "predicate": eq(bound(0), int(5)),
        "nonempty": {"tag": "exists_intro",
            "goal": json!({
                "tag": "exists", "name": "m", "sort": "int", "body":
                {"tag": "and",
                    "left": not(lt(bound(0), int(5))),
                    "right": eq(bound(0), int(5))}
            }),
            "witness": int(5),
            "proof": {"tag": "and_intro",
                "left": {"tag": "core_law", "id": "lt_irrefl", "args": [int(5)]},
                "right": {"tag": "refl", "term": int(5)}}}
    });
    (target, proof)
}

#[test]
fn proves_a_witnessed_predicate_has_a_least_element() {
    let (target, proof) = least();
    let checked = verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
    assert!(checked.judgment.custom_axioms.is_empty());
    assert!(checked.steps.iter().any(|step| step.rule == "least"));
}

#[test]
fn rejects_least_without_a_witness() {
    let (target, mut proof) = least();
    proof["nonempty"] = json!({"tag": "refl", "term": int(5)});
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(error.contains("requires a nonempty witness"), "{error}");
}

#[test]
fn accepts_the_new_integer_laws() {
    let zero_lt_one = json!({"tag": "implies_elim",
        "implication": {"tag": "core_law", "id": "lt_succ_rev", "args": [int(0), int(0)]},
        "premise": {"tag": "core_law", "id": "lt_irrefl", "args": [int(0)]}});
    let cases = [
        (
            lt(int(0), int(1)),
            json!({"tag": "implies_elim",
                "implication": {"tag": "implies_elim",
                    "implication": {"tag": "core_law", "id": "mul_pos", "args": [int(1), int(1)]},
                    "premise": zero_lt_one.clone()},
                "premise": zero_lt_one}),
        ),
        (
            implies(
                eq(int(5), int(1)),
                or(eq(int(1), int(1)), eq(int(1), int(-1))),
            ),
            json!({"tag": "implies_intro", "binder": "h", "premise": eq(int(5), int(1)), "body":
                {"tag": "or_intro_l", "proof": {"tag": "refl", "term": int(1)},
                 "other": eq(int(1), int(-1))}}),
        ),
        (
            implies(not(lt(int(0), int(0))), lt(int(0), int(1))),
            json!({"tag": "implies_intro", "binder": "h", "premise": not(lt(int(0), int(0))), "body":
                {"tag": "implies_elim",
                 "implication": {"tag": "core_law", "id": "lt_succ_rev", "args": [int(0), int(0)]},
                 "premise": {"tag": "hyp_ref", "binder": "h"}}}),
        ),
        (
            implies(
                not(lt(int(1), int(1))),
                implies(not(lt(int(1), int(1))), eq(int(1), int(1))),
            ),
            json!({"tag": "implies_intro", "binder": "h1", "premise": not(lt(int(1), int(1))), "body":
                {"tag": "implies_intro", "binder": "h2", "premise": not(lt(int(1), int(1))), "body":
                {"tag": "implies_elim",
                 "implication": {"tag": "implies_elim",
                    "implication": {"tag": "core_law", "id": "eq_of_not_lt_not_lt", "args": [int(1), int(1)]},
                    "premise": {"tag": "hyp_ref", "binder": "h1"}},
                 "premise": {"tag": "hyp_ref", "binder": "h2"}}}}),
        ),
        (
            implies(not(not(lt(int(0), int(1)))), lt(int(0), int(1))),
            json!({"tag": "implies_intro", "binder": "h", "premise": not(not(lt(int(0), int(1)))), "body":
                {"tag": "implies_elim",
                 "implication": {"tag": "core_law", "id": "lt_dne", "args": [int(0), int(1)]},
                 "premise": {"tag": "hyp_ref", "binder": "h"}}}),
        ),
    ];
    for (target, proof) in cases {
        verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
    }
}

#[test]
fn rejects_mismatched_successor_law_arguments() {
    let target = implies(not(lt(int(0), int(0))), lt(int(0), int(1)));
    let proof = json!({"tag": "implies_intro", "binder": "h", "premise": not(lt(int(0), int(0))), "body":
        {"tag": "implies_elim",
         "implication": {"tag": "core_law", "id": "lt_succ_rev", "args": [int(1), int(0)]},
         "premise": {"tag": "hyp_ref", "binder": "h"}}});
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(
        error.contains("antecedent does not match") || error.contains("conclusion mismatch"),
        "{error}"
    );
}
