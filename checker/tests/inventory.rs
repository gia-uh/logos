use logos_checker::{CORE_LAWS, verify};
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

fn bound(index: usize) -> Value {
    json!({"tag": "bound", "index": index})
}

#[test]
fn the_published_inventory_is_versioned_and_unique() {
    let commands: Value =
        serde_json::from_str(include_str!("../src/commands.json")).expect("commands.json parses");
    assert_eq!(commands["protocol_version"], 1);
    assert_eq!(commands["proof_formats"], json!(["logos-proof-v1"]));
    assert_eq!(commands["theories"], json!(["logos-core-v1"]));
    let published = commands["proof_format"]["core_laws"]
        .as_array()
        .expect("core_laws is a list");
    assert_eq!(published.len(), CORE_LAWS.len());
    let mut unique = std::collections::HashSet::new();
    for law in published {
        assert!(unique.insert(law.as_str().expect("law IDs are strings")));
    }
}

#[test]
fn rejects_an_unpublished_law_id() {
    let target = json!({"tag": "lt", "left": {"tag": "int", "value": "0"}, "right": {"tag": "int", "value": "1"}});
    let proof = json!({"tag": "core_law", "id": "invented_order_law", "args": []});
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(error.contains("unknown core law"), "{error}");
}

#[test]
fn rejects_the_wrong_number_of_substitutions() {
    let target = json!({"tag": "eq", "left": {"tag": "int", "value": "0"}, "right": {"tag": "int", "value": "0"}});
    let proof = json!({"tag": "core_law", "id": "add_zero", "args": [
        {"tag": "int", "value": "0"}, {"tag": "int", "value": "1"}
    ]});
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(error.contains("requires 1 substitutions"), "{error}");
}

#[test]
fn rejects_a_sequence_law_instantiated_at_an_integer() {
    let zero = json!({"tag": "int", "value": "0"});
    let target = json!({"tag": "le", "left": zero.clone(), "right": {"tag": "len", "seq": zero}});
    let proof = json!({"tag": "core_law", "id": "length_nonneg", "args": [
        {"tag": "int", "value": "0"}
    ]});
    let error = verify(&bundle(target, proof)).err().unwrap();
    assert!(error.contains("has sort int, expected seq"), "{error}");
}

#[test]
fn reports_a_sequence_substitution_with_its_real_sort() {
    let xs = json!({"tag": "bound", "index": 2});
    let i = bound(1);
    let j = bound(0);
    let body = json!({"tag": "implies", "left": {"tag": "sorted", "seq": xs.clone()}, "right":
        {"tag": "implies", "left": {"tag": "le", "left": {"tag": "int", "value": "0"}, "right": i.clone()}, "right":
        {"tag": "implies", "left": {"tag": "le", "left": i.clone(), "right": j.clone()}, "right":
        {"tag": "implies", "left": {"tag": "lt", "left": j.clone(), "right": {"tag": "len", "seq": xs.clone()}}, "right":
        {"tag": "le", "left": {"tag": "nth", "seq": xs.clone(), "index": i}, "right":
            {"tag": "nth", "seq": xs.clone(), "index": j}}}}}});
    let target = json!({"tag": "forall", "name": "xs", "sort": "seq", "body":
        {"tag": "forall", "name": "i", "sort": "int", "body":
        {"tag": "forall", "name": "j", "sort": "int", "body": body}}});
    let proof = json!({"tag": "forall_intro", "name": "xs", "sort": "seq", "body":
        {"tag": "forall_intro", "name": "i", "sort": "int", "body":
        {"tag": "forall_intro", "name": "j", "sort": "int", "body":
        {"tag": "core_law", "id": "sorted_elim", "args": [xs, i, j]}}}});
    let checked = verify(&bundle(target, proof)).unwrap_or_else(|error| panic!("{error}"));
    let step = checked
        .steps
        .iter()
        .find(|step| step.rule == "core_law")
        .expect("checked law step");
    let law = step.law.as_ref().expect("law application");
    assert_eq!(law.id, "sorted_elim");
    let sorts: Vec<&str> = law
        .substitution
        .iter()
        .map(|item| item.sort.name())
        .collect();
    assert_eq!(sorts, ["seq", "int", "int"]);
}

#[test]
fn a_declaration_cannot_take_a_published_law_id() {
    let mut bytes = bundle(
        json!({"tag": "eq", "left": bound(0), "right": bound(0)}),
        json!({"tag": "refl", "term": bound(0)}),
    );
    let mut data: Value = serde_json::from_slice(&bytes).unwrap();
    data["declarations"] = json!([{"id": "le_refl", "name": "le_refl", "sort": "int"}]);
    bytes = serde_json::to_vec(&data).unwrap();
    let error = verify(&bytes).err().unwrap();
    assert!(error.contains("reserved by logos-core-v1"), "{error}");
}

#[test]
fn the_manual_names_every_published_law() {
    let manual = include_str!("../../docs/portable-proof-format.md");
    for law in CORE_LAWS {
        assert!(manual.contains(&format!("`{}`", law.id)), "{}", law.id);
    }
    assert!(!manual.contains("Existential elimination and other domains remain milestone work"));
}

#[test]
fn prior_certificates_still_verify_with_the_same_digest() {
    for (name, digest) in [
        (
            "arithmetic.logos",
            "42a0f93c3fbb94c06047ba47a2cffa4d98356e13ddc31b4499de5c612254f60f",
        ),
        (
            "authorization.logos",
            "63ebdcec25bfe9f5f65b84c84315a390db4f529115fbc0067b37d34e93d9f325",
        ),
        (
            "dependencies.logos",
            "b45449f90011069ed8670f97ee71006635e26c34b0cdcf314e8dff868fedbba2",
        ),
        (
            "primes.logos",
            "92ffee83300604fe2ab1c2a10e201a42322248beab82f147468836f445a71825",
        ),
        (
            "shared-label.logos",
            "b0568ef8f6d7e51e90b8211937ca5ff6644373d6858f61286e08dff70ceb3ba6",
        ),
    ] {
        let bytes = std::fs::read(format!("tests/fixtures/portable/{name}")).unwrap();
        let checked = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || verify(&bytes))
            .unwrap()
            .join()
            .unwrap()
            .unwrap_or_else(|error| panic!("{name}: {error}"));
        assert_eq!(checked.judgment.artifact_sha256, digest, "{name}");
        assert_eq!(checked.judgment.format, "logos-proof-v1");
        assert_eq!(checked.judgment.theory, "logos-core-v1");
    }
}
