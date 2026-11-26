use logos_checker::{Verified, verify};
use serde_json::{Value, json};

fn symbol(id: &str) -> Value {
    json!({"tag": "symbol", "id": id})
}

fn hyp(binder: &str) -> Value {
    json!({"tag": "hyp_ref", "binder": binder})
}

fn binary(tag: &str, left: &Value, right: &Value) -> Value {
    json!({"tag": tag, "left": left, "right": right})
}

fn introduce(binder: &str, premise: &Value, body: Value) -> Value {
    json!({"tag": "implies_intro", "binder": binder, "premise": premise, "body": body})
}

fn check(target: Value, proof: Value) -> Result<Verified, String> {
    check_with(target, proof, json!([]), json!([]))
}

fn check_with(
    target: Value,
    proof: Value,
    custom_axioms: Value,
    lemmas: Value,
) -> Result<Verified, String> {
    verify(
        &serde_json::to_vec(&json!({
            "format": "logos-proof-v1",
            "theory": "logos-core-v1",
            "declarations": [
                {"id": "p", "name": "P", "sort": "prop"},
                {"id": "q", "name": "Q", "sort": "prop"},
            ],
            "custom_axioms": custom_axioms,
            "lemmas": lemmas,
            "target": target,
            "proof": proof,
        }))
        .unwrap(),
    )
}

fn cases(left: Value, right: Value) -> Value {
    json!({"tag": "or_elim", "proof": hyp("sum"), "binder": "case", "left": left, "right": right})
}

fn flip_cases() -> Value {
    cases(
        json!({"tag": "or_intro_r", "proof": hyp("case"), "other": symbol("q")}),
        json!({"tag": "or_intro_l", "proof": hyp("case"), "other": symbol("p")}),
    )
}

#[test]
fn cases_bind_their_own_disjunct_and_restore_the_outer_hypothesis() {
    let (p, q) = (symbol("p"), symbol("q"));
    let sum = binary("or", &p, &q);
    let flip = binary("or", &q, &p);
    let conclusion = binary("and", &flip, &q);
    let target = binary("implies", &sum, &binary("implies", &q, &conclusion));
    let proof = introduce(
        "sum",
        &sum,
        introduce("case", &q, binary("and_intro", &flip_cases(), &hyp("case"))),
    );
    let checked = check(target, proof).unwrap();
    let case = checked
        .steps
        .iter()
        .find(|step| step.rule == "or_elim")
        .unwrap();
    let [left, right] = case.discharged_cases.as_ref().unwrap();
    assert_ne!(left, right);
    for (assumption, other, label) in [(left, right, "P"), (right, left, "Q")] {
        let reference = checked
            .steps
            .iter()
            .find(|step| step.rule == "hyp_ref" && step.premises == [assumption.as_str()])
            .unwrap();
        let context = &checked.contexts[reference.context_id];
        assert_eq!(reference.conclusion_text, label);
        assert!(context.hypotheses.iter().any(|hyp| &hyp.id == assumption));
        assert!(!context.hypotheses.iter().any(|hyp| &hyp.id == other));
    }
    let restored = checked
        .steps
        .iter()
        .find(|step| step.id == "proof.body.body.right")
        .unwrap();
    assert_eq!(restored.premises, ["proof.body.assumption"]);
    let outer = &checked.contexts[case.context_id];
    assert!(
        outer
            .hypotheses
            .iter()
            .all(|hyp| &hyp.id != left && &hyp.id != right)
    );
    assert!(checked.judgment.custom_axioms.is_empty());
}

#[test]
fn rejects_leaked_cases_and_wrong_case_premises() {
    let (p, q) = (symbol("p"), symbol("q"));
    let sum = binary("or", &p, &q);
    let flip = binary("or", &q, &p);
    let target = binary("implies", &sum, &flip);
    for (premise, proof, expected) in [
        (
            &sum,
            cases(hyp("case"), hyp("case")),
            "case branches prove different conclusions",
        ),
        (
            &sum,
            cases(hyp("case"), hyp("missing")),
            "out-of-scope hypothesis",
        ),
        (
            &sum,
            binary("and_intro", &flip_cases(), &hyp("case")),
            "out-of-scope hypothesis",
        ),
        (&p, flip_cases(), "or_elim requires a disjunction"),
    ] {
        let proof = introduce("sum", premise, proof);
        let error = check(target.clone(), proof).err().unwrap();
        assert!(error.contains(expected), "{error}");
    }
}

#[test]
fn checks_dependencies_reached_only_by_the_right_branch() {
    let (p, q) = (symbol("p"), symbol("q"));
    let sum = binary("or", &p, &q);
    let target = binary("implies", &sum, &p);
    let proof = introduce(
        "sum",
        &sum,
        cases(hyp("case"), json!({"tag": "theorem_ref", "id": "L"})),
    );
    let checked = check_with(
        target,
        proof,
        json!([{"id": "A", "statement": p}]),
        json!([{"id": "L", "statement": p, "proof": {"tag": "axiom_ref", "id": "A"}}]),
    )
    .unwrap();
    assert_eq!(checked.judgment.custom_axioms[0].id, "A");
    let right_assumption = checked
        .steps
        .iter()
        .find(|step| step.id == "proof.body.right.assumption")
        .unwrap();
    assert_eq!(right_assumption.conclusion_text, "Q");
}

#[test]
fn rejects_missing_mismatched_or_ill_sorted_rule_premises() {
    let (p, q) = (symbol("p"), symbol("q"));
    let not_p = json!({"tag": "not", "operand": p});
    let falsehood = json!({"tag": "false"});
    let zero = json!({"tag": "int", "value": "0"});
    let valid_falsehood = json!({"tag": "not_elim", "negation": hyp("not_p"), "premise": hyp("p")});
    for (rule, expected) in [
        (
            json!({"tag": "or_intro_l", "proof": hyp("p"), "other": zero}),
            "has sort int, expected prop",
        ),
        (
            json!({"tag": "not_intro", "proof": introduce("h", &p, hyp("h"))}),
            "not_intro requires an implication to falsehood",
        ),
        (
            json!({"tag": "not_elim", "negation": hyp("not_p"), "premise": hyp("q")}),
            "negation operand does not match premise",
        ),
        (
            json!({"tag": "not_elim", "negation": hyp("p"), "premise": hyp("p")}),
            "not_elim requires a negation",
        ),
        (
            json!({"tag": "ex_falso", "proof": hyp("not_p"), "conclusion": q}),
            "ex_falso requires a proof of falsehood",
        ),
        (
            json!({"tag": "ex_falso", "conclusion": q}),
            "missing field \x60proof\x60",
        ),
        (
            json!({"tag": "ex_falso", "proof": valid_falsehood, "conclusion": zero}),
            "has sort int, expected prop",
        ),
        (
            json!({"tag": "implies_elim", "implication": introduce("h", &p, hyp("h")), "premise": hyp("q")}),
            "implication antecedent does not match premise",
        ),
        (
            json!({"tag": "implies_elim", "implication": hyp("p"), "premise": hyp("p")}),
            "implies_elim requires an implication",
        ),
    ] {
        let proof = introduce(
            "p",
            &p,
            introduce("q", &q, introduce("not_p", &not_p, rule)),
        );
        let error = check(falsehood.clone(), proof).err().unwrap();
        assert!(error.contains(expected), "{error}");
    }

    let bad_not = json!({"tag": "not", "operand": zero});
    let error = check(bad_not, valid_falsehood).err().unwrap();
    assert!(error.contains("has sort int, expected prop"), "{error}");
}

#[test]
fn falsehood_is_a_proposition_with_elimination_and_no_introduction() {
    let p = symbol("p");
    let falsehood = json!({"tag": "false"});
    let proof = introduce(
        "absurd",
        &falsehood,
        json!({
            "tag": "ex_falso", "proof": hyp("absurd"), "conclusion": p
        }),
    );
    let checked = check(binary("implies", &falsehood, &p), proof).unwrap();
    assert_eq!(checked.judgment.statement_text, "⊥ → P");
    let error = check(falsehood.clone(), falsehood).err().unwrap();
    assert!(error.contains("unknown variant"), "{error}");
}
