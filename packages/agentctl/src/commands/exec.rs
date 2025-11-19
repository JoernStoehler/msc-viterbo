use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};

use clap::Args;
use serde::Deserialize;

use crate::{
    error::CliError,
    state::{Database, TurnStatus},
};

#[derive(Args, Clone)]
pub struct ExecArgs {
    #[arg(long)]
    pub handle: String,
    #[arg(long = "turn-id")]
    pub turn_id: i64,
    #[arg(long)]
    pub worktree: PathBuf,
    #[arg(long = "prompt-file")]
    pub prompt_file: PathBuf,
    #[arg(long = "log-path")]
    pub log_path: PathBuf,
    #[arg(long = "final-path")]
    pub final_path: PathBuf,
    #[arg(long = "repo-root")]
    pub repo_root: PathBuf,
    #[arg(long = "model")]
    pub model: String,
    #[arg(long = "budget")]
    pub budget: String,
    #[arg(long = "resume-uuid")]
    pub resume_uuid: Option<String>,
}

pub fn run(args: ExecArgs) -> Result<(), CliError> {
    let mut db = Database::open(&args.repo_root)?;
    let mut log_file = File::create(&args.log_path)
        .map_err(|err| CliError::new(70, format!("Failed to open log file: {err}")))?;
    let prompt_file = File::open(&args.prompt_file)
        .map_err(|err| CliError::new(70, format!("Failed to open prompt file: {err}")))?;

    let mut cmd = Command::new("codex");
    cmd.arg("exec")
        .arg("--json")
        .arg("--sandbox")
        .arg("danger-full-access")
        .arg("-C")
        .arg(&args.worktree)
        .arg("--model")
        .arg(&args.model)
        .arg("--output-last-message")
        .arg(&args.final_path)
        .stdin(Stdio::from(prompt_file))
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    if let Some(uuid) = &args.resume_uuid {
        cmd.arg("resume").arg(uuid).arg("-");
    } else {
        cmd.arg("-");
    }

    let mut child = match cmd.spawn() {
        Ok(child) => child,
        Err(err) => {
            println!("ERROR failed to spawn codex exec");
            return Err(CliError::new(
                73,
                format!("Failed to spawn codex exec: {err}"),
            ));
        }
    };

    let stderr = child.stderr.take().unwrap();
    let stderr_path = args.log_path.clone();
    std::thread::spawn(move || {
        let reader = BufReader::new(stderr).lines();
        if let Ok(mut file) = File::options().create(true).append(true).open(&stderr_path) {
            for line in reader.map_while(Result::ok) {
                let _ = writeln!(file, "STDERR {}", line);
            }
        }
    });

    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| CliError::new(70, "codex exec missing stdout".to_string()))?;
    let mut reader = BufReader::new(stdout);
    let mut line = String::new();
    let expected_uuid = args.resume_uuid.clone();
    let mut session_uuid: Option<String> = None;

    while reader
        .read_line(&mut line)
        .map_err(|err| CliError::new(70, format!("Failed to read codex output: {err}")))?
        > 0
    {
        let trimmed = line.trim_end();
        writeln!(log_file, "{trimmed}").ok();
        if session_uuid.is_some() {
            line.clear();
            continue;
        }
        if let Some(uuid) = extract_session_id(trimmed) {
            if let Some(expected) = &expected_uuid
                && uuid != *expected
            {
                println!(
                    "ERROR session-id-mismatch expected {} got {}",
                    expected, uuid
                );
                let _ = child.kill();
                db.mark_turn_failed(args.turn_id, "session uuid mismatch")?;
                return Err(CliError::new(
                    74,
                    "Resume returned different session uuid".to_string(),
                ));
            }
            session_uuid = Some(uuid.clone());
            println!("SESSION {uuid}");
            std::io::stdout().flush().ok();
        }
        line.clear();
    }

    let _session_uuid = match session_uuid {
        Some(id) => id,
        None => {
            println!("ERROR session-id-missing");
            db.mark_turn_failed(args.turn_id, "session uuid missing")?;
            return Err(CliError::new(74, "Session UUID missing".to_string()));
        }
    };

    let status = child
        .wait()
        .map_err(|err| CliError::new(70, format!("Failed to wait on codex: {err}")))?;
    if status.success() {
        db.mark_turn_stopped(args.turn_id, TurnStatus::Stopped, None)?;
        Ok(())
    } else {
        db.mark_turn_failed(args.turn_id, "codex exec exited with failure")?;
        println!("ERROR codex exec failed");
        Err(CliError::new(73, "codex exec failed".to_string()))
    }
}

fn extract_session_id(line: &str) -> Option<String> {
    #[derive(Deserialize)]
    struct Payload {
        id: Option<String>,
        thread_id: Option<String>,
    }
    #[derive(Deserialize)]
    struct ThreadEvent {
        #[serde(rename = "type")]
        _event_type: Option<String>,
        thread_id: Option<String>,
        payload: Option<Payload>,
    }
    match serde_json::from_str::<ThreadEvent>(line) {
        Ok(ev) => ev
            .thread_id
            .or_else(|| ev.payload.and_then(|p| p.thread_id.or(p.id))),
        Err(_) => None,
    }
}
