use logos_checker::verify;
use serde_json::{Value, json};

fn bundle(target: Value, proof: Value) -> Value {
    json!({
        "format": "logos-proof-v1",
        "theory": "logos-core-v1",
        "name": "author label",
        "declarations": [],
        "custom_axioms": [],
        "lemmas": [],
        "target": target,
        "proof": proof,
    })
}

fn bound(index: usize) -> Value {
    json!({"tag": "bound", "index": index})
}

fn int(value: &str) -> Value {
    json!({"tag": "int", "value": value})
}

fn binary(tag: &str, left: Value, right: Value) -> Value {
    json!({"tag": tag, "left": left, "right": right})
}

fn quantified(name: &str, body: Value) -> Value {
    json!({"tag": "forall", "name": name, "sort": "int", "body": body})
}

fn introduce(name: &str, body: Value) -> Value {
    json!({"tag": "forall_intro", "name": name, "sort": "int", "body": body})
}

fn refl(term: Value) -> Value {
    json!({"tag": "refl", "term": term})
}

fn run(file: &Value) -> logos_checker::Verified {
    verify(&serde_json::to_vec(file).unwrap()).unwrap_or_else(|error| panic!("{error}: {file}"))
}

fn reject(file: &Value, diagnostic: &str) {
    let error = verify(&serde_json::to_vec(file).unwrap())
        .err()
        .expect("invalid proof accepted");
    assert!(error.contains(diagnostic), "{error}");
}

#[test]
fn reflexivity_checks_alpha_equivalence_and_rejects_scope_and_sort_errors() {
    let mut file = bundle(
        quantified("x", binary("eq", bound(0), bound(0))),
        introduce("renamed", refl(bound(0))),
    );
    let checked = run(&file);
    assert_eq!(checked.judgment.statement_text, "∀x:int, x = x");
    let refl_step = serde_json::to_value(&checked.steps[0]).unwrap();
    assert_eq!(refl_step["conclusion_sort"], "prop");
    assert_eq!(refl_step["conclusion_text"], "renamed = renamed");
    let root = serde_json::to_value(&checked.steps[1]).unwrap();
    assert!(root["conclusion_conversion"]["common_normal_form"].is_object());
    assert_eq!(root["introduced_variable"], "proof.variable");

    file["target"] = quantified("x", quantified("y", binary("eq", bound(1), bound(0))));
    file["proof"] = introduce("x", introduce("y", refl(bound(1))));
    reject(&file, "proof conclusion mismatch");
    file["proof"]["body"]["body"]["term"] = bound(2);
    reject(&file, "out-of-scope bound variable");
    file["target"]["body"]["sort"] = json!("prop");
    reject(&file, "has sort prop, expected int");
}

#[test]
fn law_instances_are_checked_and_ids_are_reserved() {
    let mut file: Value =
        serde_json::from_str(include_str!("fixtures/portable/arithmetic.logos")).unwrap();
    let checked = run(&file);
    let trace = checked
        .steps
        .iter()
        .find(|step| step.rule == "core_law")
        .unwrap();
    let step = serde_json::to_value(trace).unwrap();
    let scope = serde_json::to_value(&checked.contexts[trace.context_id]).unwrap();
    assert_eq!(
        step["provenance"],
        json!({"kind": "core_law", "id": "add_comm"})
    );
    assert!(step["explanation"].as_str().unwrap().contains("swap"));
    assert_eq!(
        step["law"]["substitution"],
        json!([
            {"formal":"a","sort":"int","actual":{"tag":"bound","index":0}},
            {"formal":"b","sort":"int","actual":{"tag":"bound","index":1}}
        ])
    );
    assert_eq!(scope["variables"][0]["name"], "x");
    assert_eq!(scope["variables"][1]["name"], "y");
    assert_eq!(scope["variables"][1]["sort"], "int");

    let original = file.clone();
    file["proof"]["body"]["body"]["steps"][0]["args"][1] = bound(0);
    reject(&file, "proof conclusion mismatch");
    file = original.clone();
    file["proof"]["body"]["body"]["steps"][0]["id"] = json!("mul_zero");
    reject(&file, "unknown core law");
    file = original.clone();
    file["proof"]["body"]["body"]["steps"][0]["args"] = json!([bound(0)]);
    reject(&file, "requires 2 substitutions");
    file = original.clone();
    file["custom_axioms"] = json!([{"id": "add_comm", "statement": file["target"]}]);
    reject(&file, "reserved by logos-core-v1");
    file = original;
    file["proof"]["body"]["body"]["steps"][0] = json!({"tag":"step_ref","index":1});
    reject(&file, "out-of-scope block step");
}

#[test]
fn definition_unfolding_and_instantiation_are_capture_avoiding() {
    let app = |id: &str, args: Vec<Value>| json!({"tag":"app","id":id,"args":args});
    let mut file = bundle(
        quantified("outer", app("R", vec![bound(0)])),
        introduce("u", introduce("u", refl(bound(1)))),
    );
    file["functions"] = json!([{
        "id": "R", "name": "R", "params": ["int"], "result": "prop",
        "body": quantified("inner", binary("eq", bound(1), bound(1))),
    }]);
    run(&file);
    file["proof"]["body"]["body"]["term"] = bound(0);
    reject(&file, "proof conclusion mismatch");

    file["target"] = quantified(
        "outer",
        quantified("inner", binary("eq", bound(1), bound(1))),
    );
    file["proof"] = introduce(
        "outer",
        json!({
            "tag": "forall_elim",
            "term": bound(0),
            "proof": introduce("a", introduce("b", refl(bound(1)))),
        }),
    );
    run(&file);
    file["declarations"] = json!([{"id":"P","name":"P","sort":"prop"}]);
    file["proof"]["body"]["term"] = json!({"tag":"symbol","id":"P"});
    reject(&file, "has sort prop, expected int");
}

#[test]
fn scopes_lift_active_hypotheses_under_fresh_variables_and_discharge_them() {
    let equality = |index| binary("eq", bound(index), bound(index));
    let mut file = bundle(
        quantified(
            "x",
            binary("implies", equality(0), quantified("x", equality(1))),
        ),
        introduce(
            "x",
            json!({
                "tag": "implies_intro", "binder": "h", "premise": equality(0),
                "body": introduce("x", json!({"tag":"hyp_ref","binder":"h"})),
            }),
        ),
    );
    let checked = run(&file);
    let step = checked
        .steps
        .iter()
        .find(|step| step.rule == "hyp_ref")
        .unwrap();
    let scope = serde_json::to_value(&checked.contexts[step.context_id]).unwrap();
    assert_eq!(scope["variables"].as_array().unwrap().len(), 2);
    assert_ne!(scope["variables"][0]["id"], scope["variables"][1]["id"]);
    assert_eq!(scope["hypotheses"][0]["binder_depth"], 1);
    let trace = serde_json::to_value(&checked.steps).unwrap();
    assert_eq!(trace[1]["conclusion"], equality(1));
    assert_eq!(trace[1]["provenance"]["proof_step"], trace[0]["id"]);
    assert_eq!(trace[3]["discharged"], trace[0]["id"]);
    assert_eq!(
        checked.contexts[checked.steps[3].context_id]
            .hypotheses
            .len(),
        0
    );
    file["target"]["body"]["right"]["body"] = equality(0);
    reject(&file, "proof conclusion mismatch");
}

#[test]
fn conversion_computes_large_integers_and_preserves_opaque_identities() {
    let pow = json!({"tag":"pow","base":int("2"),"exponent":256});
    let expected =
        int("115792089237316195423570985008687907853269984665640564039457584007913129639936");
    let mut file = bundle(binary("eq", pow.clone(), expected), refl(pow));
    run(&file);
    file["target"]["left"]["exponent"] = json!(-1);
    reject(&file, "malformed proof file");
    file["target"]["left"]["exponent"] = bound(0);
    reject(&file, "malformed proof file");

    let app = |id, arg| json!({"tag":"app","id":id,"args":[arg]});
    file["functions"] = json!([
        {"id":"f","name":"same","params":["int"],"result":"int"},
        {"id":"g","name":"same","params":["int"],"result":"int"}
    ]);
    file["target"] = quantified("x", binary("eq", app("f", bound(0)), app("g", bound(0))));
    file["proof"] = introduce("x", refl(app("f", bound(0))));
    reject(&file, "proof conclusion mismatch");
}

#[test]
fn equality_rules_check_their_premises_and_blocks_skip_dead_dependencies() {
    let mut file = bundle(
        binary("eq", int("2"), int("2")),
        json!({
            "tag":"trans","left":refl(int("2")),"right":refl(int("3"))
        }),
    );
    reject(&file, "middle terms do not match");
    file["proof"] = json!({
        "tag":"block","result":2,"steps":[
            {"tag":"theorem_ref","id":"unused"},
            refl(int("2")),
            {"tag":"step_ref","index":1}
        ]
    });
    let checked = run(&file);
    assert_eq!(checked.steps.len(), 3);
    file["proof"] = json!({"tag":"step_ref","index":0});
    reject(&file, "out-of-scope block step");
    file["proof"] = json!({"tag":"congr","context":bound(1),"proof":refl(int("2"))});
    reject(&file, "out-of-scope bound variable");
}
