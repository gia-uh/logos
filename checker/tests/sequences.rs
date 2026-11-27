use logos_checker::verify;
use serde_json::{Value, json};

fn bound(index: usize) -> Value {
    json!({"tag": "bound", "index": index})
}

fn int(value: &str) -> Value {
    json!({"tag": "int", "value": value})
}

fn le(left: Value, right: Value) -> Value {
    json!({"tag": "le", "left": left, "right": right})
}

fn lt(left: Value, right: Value) -> Value {
    json!({"tag": "lt", "left": left, "right": right})
}

fn len(seq: Value) -> Value {
    json!({"tag": "len", "seq": seq})
}

fn nth(seq: Value, index: Value) -> Value {
    json!({"tag": "nth", "seq": seq, "index": index})
}

fn sorted(seq: Value) -> Value {
    json!({"tag": "sorted", "seq": seq})
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

fn intro(name: &str, sort: &str, body: Value) -> Value {
    json!({"tag": "forall_intro", "name": name, "sort": sort, "body": body})
}

fn forall(name: &str, sort: &str, body: Value) -> Value {
    json!({"tag": "forall", "name": name, "sort": sort, "body": body})
}

fn assume(name: &str, premise: Value, body: Value) -> Value {
    json!({"tag": "implies_intro", "binder": name, "premise": premise, "body": body})
}

#[test]
fn sorted_lower_transports_a_strict_bound() {
    let xs = bound(3);
    let i = bound(2);
    let mid = bound(1);
    let target = bound(0);
    let premises = [
        sorted(xs.clone()),
        le(int("0"), i.clone()),
        le(i.clone(), mid.clone()),
        lt(mid.clone(), len(xs.clone())),
        lt(nth(xs.clone(), mid.clone()), target.clone()),
    ];
    let mut body = json!({
        "tag": "core_law", "id": "sorted_lower",
        "args": [xs.clone(), i.clone(), mid.clone(), target.clone()]
    });
    for name in ["hs", "h0", "him", "hm", "h"] {
        body = json!({"tag": "implies_elim", "implication": body,
                      "premise": {"tag": "hyp_ref", "binder": name}});
    }
    let mut proof = body;
    for (name, premise) in ["h", "hm", "him", "h0", "hs"]
        .iter()
        .zip(premises.iter().rev())
    {
        proof = assume(name, premise.clone(), proof);
    }
    proof = intro("t", "int", proof);
    proof = intro("mid", "int", proof);
    proof = intro("i", "int", proof);
    proof = intro("xs", "seq", proof);
    let mut statement = lt(nth(bound(3), bound(2)), bound(0));
    for premise in premises.iter().rev() {
        statement = json!({"tag": "implies", "left": premise, "right": statement});
    }
    let mut target = forall(
        "xs",
        "seq",
        forall(
            "i",
            "int",
            forall("mid", "int", forall("t", "int", statement)),
        ),
    );
    verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
}

#[test]
fn length_is_non_negative() {
    let target = forall("xs", "seq", le(int("0"), len(bound(0))));
    let proof = intro(
        "xs",
        "seq",
        json!({
            "tag": "core_law", "id": "length_nonneg", "args": [bound(0)]
        }),
    );
    verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
}

#[test]
fn rejects_a_sequence_where_an_integer_is_expected() {
    let target = json!({"tag": "forall", "name": "xs", "sort": "seq", "body":
        {"tag": "eq", "left": bound(0), "right": int("0")}});
    let proof = intro("xs", "seq", json!({"tag": "refl", "term": bound(0)}));
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(
        error.contains("expected seq") || error.contains("has sort int"),
        "{error}"
    );
}
