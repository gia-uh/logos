mod markdown;

use logos_checker::{
    Annotations, Judgment, MAX_ARTIFACT_BYTES, PROTOCOL_VERSION, Step, TraceContext, verify,
};
use serde::Serialize;
use std::{
    env, fs,
    io::{self, Read, Write},
    path::Path,
    process::ExitCode,
};

const HELP: &str = include_str!("help.txt");
const COMMANDS: &str = include_str!("commands.json");
const EXAMPLE: &str = include_str!("../examples/authorization.py");
const ARITHMETIC_EXAMPLE: &str = include_str!("../examples/arithmetic.py");
const ARITHMETIC_FIXTURE: &str = include_str!("../tests/fixtures/portable/arithmetic.logos");
const DEPENDENCY_EXAMPLE: &str = include_str!("../examples/dependencies.py");
const DEPENDENCY_FIXTURE: &str = include_str!("../tests/fixtures/portable/dependencies.logos");
const GUIDED_KNIGHTS_KNAVES_EXAMPLE: &str = include_str!("../examples/guide_knights_knaves.py");
const KNIGHTS_KNAVES_EXAMPLE: &str = include_str!("../examples/solve_knights_knaves.py");
const PRIMES_EXAMPLE: &str = include_str!("../examples/primes.py");
const PRIMES_FIXTURE: &str = include_str!("../tests/fixtures/portable/primes.logos");
const FIXTURE: &str = include_str!("../tests/fixtures/portable/authorization.logos");

#[derive(Serialize)]
struct Inspection<'a> {
    #[serde(flatten)]
    judgment: &'a Judgment,
    steps: &'a [Step],
    contexts: &'a [TraceContext],
    annotations: &'a Annotations,
    claim: Claim,
}

#[derive(Serialize)]
struct Claim {
    statement_field: &'static str,
    proof_step: &'static str,
    sort: &'static str,
}

enum Failure {
    Usage(String),
    Operation(String),
    Policy,
}

impl From<io::Error> for Failure {
    fn from(error: io::Error) -> Self {
        Self::Operation(error.to_string())
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            let (code, message) = match error {
                Failure::Policy => return ExitCode::from(3),
                Failure::Usage(message) => (2, message),
                Failure::Operation(message) => (1, message),
            };
            if args.iter().any(|arg| arg == "--json") {
                eprintln!(
                    "{}",
                    serde_json::json!({
                        "protocol_version": PROTOCOL_VERSION, "status": "error", "error": message,
                    })
                );
            } else {
                eprintln!("Error: {message}");
            }
            ExitCode::from(code)
        }
    }
}

fn run(args: &[String]) -> Result<(), Failure> {
    match args {
        [] => print!("{HELP}"),
        [arg] if arg == "--help" || arg == "-h" => print!("{HELP}"),
        [arg] if arg == "--version" => println!("logos {}", env!("CARGO_PKG_VERSION")),
        [cmd, flag] if cmd == "commands" && flag == "--json" => print!("{COMMANDS}"),
        [cmd] if cmd == "example" => emit_example([
            ("authorization.logos", FIXTURE),
            ("authorization.py", EXAMPLE),
        ])?,
        [cmd, selection] if cmd == "example" && selection == "arithmetic" => emit_example([
            ("arithmetic.logos", ARITHMETIC_FIXTURE),
            ("arithmetic.py", ARITHMETIC_EXAMPLE),
        ])?,
        [cmd, selection] if cmd == "example" && selection == "dependencies" => emit_example([
            ("dependencies.logos", DEPENDENCY_FIXTURE),
            ("dependencies.py", DEPENDENCY_EXAMPLE),
        ])?,
        [cmd, selection] if cmd == "example" && selection == "knights-knaves" => emit_example([
            ("solve_knights_knaves.py", KNIGHTS_KNAVES_EXAMPLE),
            ("guide_knights_knaves.py", GUIDED_KNIGHTS_KNAVES_EXAMPLE),
        ])?,
        [cmd, selection] if cmd == "example" && selection == "primes" => emit_example([
            ("primes.logos", PRIMES_FIXTURE),
            ("primes.py", PRIMES_EXAMPLE),
        ])?,
        [cmd, flag]
            if matches!(cmd.as_str(), "check" | "inspect" | "example" | "commands")
                && matches!(flag.as_str(), "--help" | "-h") =>
        {
            print!("{HELP}")
        }
        [cmd, rest @ ..] if matches!(cmd.as_str(), "check" | "inspect") => {
            check_command(rest, cmd == "inspect")?;
        }
        _ => return Err(Failure::Usage("invalid arguments; see logos --help".into())),
    }
    Ok(())
}

fn emit_example(files: [(&str, &str); 2]) -> Result<(), Failure> {
    for (name, _) in files {
        if Path::new(name).symlink_metadata().is_ok() {
            return Err(Failure::Operation(format!("{name} already exists")));
        }
    }
    for (name, contents) in files {
        fs::File::create_new(name)?.write_all(contents.as_bytes())?;
        println!("Wrote {name}");
    }
    Ok(())
}

fn check_command(args: &[String], inspect: bool) -> Result<(), Failure> {
    let mut json = false;
    let mut markdown = false;
    let mut strict = false;
    let mut file = None;
    for arg in args {
        match arg.as_str() {
            "--json" if !json => json = true,
            "--markdown" if inspect && !markdown => markdown = true,
            "--strict" if !strict => strict = true,
            path if file.is_none() && (!path.starts_with('-') || path == "-") => file = Some(path),
            _ => return Err(Failure::Usage(format!("unexpected argument {arg:?}"))),
        }
    }
    if markdown && json {
        return Err(Failure::Usage(
            "--markdown and --json are mutually exclusive".into(),
        ));
    }
    let file = file.ok_or_else(|| Failure::Usage("a proof file is required".into()))?;
    let input: Box<dyn Read> = if file == "-" {
        Box::new(io::stdin().lock())
    } else {
        Box::new(fs::File::open(file)?)
    };
    let mut bytes = Vec::new();
    input
        .take((MAX_ARTIFACT_BYTES + 1) as u64)
        .read_to_end(&mut bytes)?;
    let mut checked = verify(&bytes).map_err(Failure::Operation)?;
    let judgment = &mut checked.judgment;
    let denied = strict && !judgment.custom_axioms.is_empty();
    if denied {
        judgment.status = "policy_denied";
    }
    if markdown {
        print!("{}", markdown::render(&checked));
    } else if json {
        let output = if inspect {
            serde_json::to_string(&Inspection {
                judgment,
                steps: &checked.steps,
                contexts: &checked.contexts,
                annotations: &checked.annotations,
                claim: Claim {
                    statement_field: "statement",
                    proof_step: "proof",
                    sort: "prop",
                },
            })
        } else {
            serde_json::to_string(judgment)
        };
        println!(
            "{}",
            output.map_err(|error| Failure::Operation(error.to_string()))?
        );
    } else {
        if denied {
            println!("Policy denied: custom axioms are forbidden (--strict)");
        } else {
            let count = judgment.custom_axioms.len();
            let noun = if count == 1 { "axiom" } else { "axioms" };
            println!("Verified with {count} custom {noun}");
        }
        println!("Statement   {}", judgment.statement_text);
        println!("Theory      {}", judgment.theory);
        if let Some(label) = &judgment.unverified_author_label {
            println!("Unverified author label {label:?}");
        }
        for axiom in &judgment.custom_axioms {
            println!("Assumed     {:?}: {}", axiom.id, axiom.statement_text);
            println!("Path        {}", axiom.path.join(" → "));
        }
        if inspect {
            if let Some(claim) = &checked.annotations.claim {
                println!("Author's claim (authored, not checked) {claim}");
            }
            if let Some(strategy) = &checked.annotations.strategy {
                println!("Author's strategy (authored, not checked) {strategy}");
            }
            for step in checked.steps {
                println!("{} {}: {}", step.id, step.rule, step.conclusion_text);
                println!("  {}", step.explanation);
                for note in &step.commentary {
                    println!("  Author's note (authored, not checked) {note}");
                }
                if !step.premises.is_empty() {
                    println!("  Premises: {}", step.premises.join(", "));
                }
                if let Some(id) = step.reference_id {
                    println!("  Reference: {id:?}");
                }
                if let Some(binder) = step.binder {
                    println!("  Binder: {binder:?}");
                }
                if let Some(discharged) = step.discharged {
                    println!("  Discharged: {discharged}");
                }
            }
        }
    }
    if denied { Err(Failure::Policy) } else { Ok(()) }
}
