use serde_json::{Value, json};
use std::io::Write;
use std::process::{Command, Output, Stdio};

fn inspect(args: &[&str], proof: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_logos"))
        .arg("inspect")
        .args(args)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(proof.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

#[test]
fn renders_typed_commutativity_and_named_substitution() {
    let proof = include_str!("fixtures/portable/arithmetic.logos");
    let output = inspect(&["--markdown", "--strict"], proof);
    assert!(output.status.success());
    assert_eq!(
        output.stdout,
        inspect(&["--markdown", "--strict"], proof).stdout
    );
    let markdown = String::from_utf8(output.stdout).unwrap();
    assert!(markdown.starts_with("# Checked proof\n"));
    assert!(markdown.contains(r"\forall x \in \mathbb{Z},\quad \forall y \in \mathbb{Z}"));
    assert!(markdown.contains(r#"Substitute $a \mapsto y, b \mapsto x$ into the law."#));
    assert!(markdown.contains("Uses zero custom axioms."));
    assert!(!markdown.contains("$`"));
    assert!(markdown.contains("The conclusion follows from (4)."));
    assert!(markdown.contains("be arbitrary."));
    assert!(!markdown.contains("Author's commentary"));
    assert!(!markdown.contains("proof.body"));
    assert!(!markdown.contains("earlier checked step in this block"));
    assert!(markdown.contains("\n$$\n"));
}

#[test]
fn renders_scoped_hypotheses_and_checked_lemma_provenance() {
    let proof = include_str!("fixtures/portable/authorization.logos");
    let output = inspect(&["--markdown"], proof);
    assert!(output.status.success());
    let markdown = String::from_utf8(output.stdout).unwrap();
    assert!(markdown.contains("Assume the following proposition"));
    assert!(markdown.contains("Discharge the hypothesis (1) above."));
    assert!(markdown.contains(r"\land"));
    assert!(markdown.contains(r"\implies"));

    let proof = include_str!("fixtures/portable/dependencies.logos");
    let output = inspect(&["--strict", "--markdown"], proof);
    assert_eq!(output.status.code(), Some(3));
    let markdown = String::from_utf8(output.stdout).unwrap();
    assert!(markdown.contains("Strict policy denied"));
    assert!(markdown.contains("**Assumption 1.**"));
    assert!(markdown.contains("This uses the earlier checked lemma."));
    assert!(markdown.contains("under the listed custom axioms."));
}

#[test]
fn renders_authored_commentary_and_notes_in_order() {
    let mut proof: Value =
        serde_json::from_str(include_str!("fixtures/portable/authorization.logos")).unwrap();
    proof["annotations"] = json!({
        "claim": "Compose $P$ with <script>alert(1)</script>.",
        "strategy": "Use `Q` as the intermediate step."
    });
    let body = proof["proof"]["body"].clone();
    proof["proof"]["body"] = json!({
        "tag": "note", "text": "first note with $x$ and # forged", "body": body
    });
    let body = proof["proof"]["body"].clone();
    proof["proof"]["body"] = json!({"tag": "note", "text": "second note", "body": body});

    let output = inspect(&["--markdown"], &proof.to_string());
    assert!(output.status.success());
    let markdown = String::from_utf8(output.stdout).unwrap();
    assert!(markdown.contains("## Author's commentary (not checked)"));
    assert!(markdown.contains("\\$P\\$"));
    assert!(markdown.contains("&lt;script&gt;"));
    assert!(!markdown.contains("<script>"));
    assert!(!markdown.contains("\n# forged"));
    assert!(markdown.contains("> **Author's note (authored, not checked).**"));

    let first = markdown.find("first note").unwrap();
    let second = markdown.find("second note").unwrap();
    let step_three = markdown.find("**(3)**").unwrap();
    assert!(step_three < first && first < second);

    let output = inspect(&["--json"], &proof.to_string());
    assert!(output.status.success());
    let inspected: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(
        inspected["annotations"]["claim"],
        proof["annotations"]["claim"]
    );
    assert!(inspected["steps"].as_array().unwrap().iter().any(
        |step| step["commentary"] == json!(["first note with $x$ and # forged", "second note"])
    ));
}

#[test]
fn notes_are_transparent_to_verification() {
    let mut proof: Value =
        serde_json::from_str(include_str!("fixtures/portable/wrong-projection.logos")).unwrap();
    let body = proof["proof"].clone();
    proof["proof"] = json!({"tag": "note", "text": "This cannot rescue the proof.", "body": body});
    let output = inspect(&["--markdown"], &proof.to_string());
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .contains("proof conclusion mismatch")
    );
}

#[test]
fn rejects_invalid_proofs_and_ambiguous_output_without_a_document() {
    let invalid = include_str!("fixtures/portable/wrong-projection.logos");
    let output = inspect(&["--strict", "--markdown"], invalid);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .contains("proof conclusion mismatch")
    );
    let output = inspect(&["--markdown", "--json"], invalid);
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .contains("mutually exclusive")
    );
}

#[test]
fn author_labels_and_identifiers_cannot_end_math_or_insert_markup() {
    let mut proof: Value =
        serde_json::from_str(include_str!("fixtures/portable/authorization.logos")).unwrap();
    let label = "x`\n\n# forged\n$$\n\\input{danger}<script>";
    proof["name"] = json!(label);
    proof["declarations"][0]["name"] = json!(label);
    let output = inspect(&["--markdown"], &proof.to_string());
    assert!(output.status.success());
    let markdown = String::from_utf8(output.stdout).unwrap();
    assert!(!markdown.contains(label));
    assert!(!markdown.contains("<script>"));
    assert!(!markdown.contains("\\input"));
    assert!(!markdown.contains("# forged"));
    assert!(!markdown.contains("Unverified author label"));
    assert!(markdown.contains(r"\mathrm{x\langle U+0060\rangle"));
}
