use logos_checker::{Judgment, PROTOCOL_VERSION, Step, verify};
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
const FIXTURE: &str = include_str!("../tests/fixtures/portable/authorization.logos");

#[derive(Serialize)]
struct Inspection<'a> {
    #[serde(flatten)]
    judgment: &'a Judgment,
    steps: &'a [Step],
}

enum Failure {
    Usage(String),
    Operation(String),
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
        [cmd] if cmd == "example" => emit_example()?,
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

fn emit_example() -> Result<(), Failure> {
    let files = [
        ("authorization.logos", FIXTURE),
        ("authorization.py", EXAMPLE),
    ];
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
    let mut strict = false;
    let mut file = None;
    for arg in args {
        match arg.as_str() {
            "--json" if !json => json = true,
            "--deny-custom-axioms" if !strict => strict = true,
            path if file.is_none() && (!path.starts_with('-') || path == "-") => file = Some(path),
            _ => return Err(Failure::Usage(format!("unexpected argument {arg:?}"))),
        }
    }
    let file = file.ok_or_else(|| Failure::Usage("a proof file is required".into()))?;
    let bytes = if file == "-" {
        let mut bytes = Vec::new();
        io::stdin().read_to_end(&mut bytes)?;
        bytes
    } else {
        fs::read(file)?
    };
    let checked = verify(&bytes).map_err(Failure::Operation)?;
    let judgment = &checked.judgment;
    if strict && !judgment.custom_axioms.is_empty() {
        return Err(Failure::Operation("custom axioms denied by policy".into()));
    }
    if json {
        let output = if inspect {
            serde_json::to_string(&Inspection {
                judgment,
                steps: &checked.steps,
            })
        } else {
            serde_json::to_string(judgment)
        };
        println!(
            "{}",
            output.map_err(|error| Failure::Operation(error.to_string()))?
        );
    } else {
        println!(
            "Verified with {} custom axioms",
            judgment.custom_axioms.len()
        );
        println!("Statement   {}", judgment.statement_text);
        println!("Theory      {}", judgment.theory);
        if let Some(label) = &judgment.unverified_author_label {
            println!("Unverified author label {label:?}");
        }
        if inspect {
            for step in checked.steps {
                println!("{} {}: {}", step.id, step.rule, step.conclusion_text);
                if !step.premises.is_empty() {
                    println!("  Premises: {}", step.premises.join(", "));
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
    Ok(())
}
