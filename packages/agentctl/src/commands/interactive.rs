use std::env;
use std::fs::{self, File};
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};

use clap::Args;
use serde::Deserialize;

use crate::{
    error::CliError,
    state::{self, AgentRecord, Database, TurnStatus},
    util::{canonicalize, validate_handle},
};

use super::{
    define::{BudgetArg, ModelArg, build_record},
    session::prepare_turn_dir,
};

#[derive(Args, Clone)]
pub struct InteractiveArgs {
    pub handle: String,
    #[arg(long)]
    pub allocate: bool,
    #[arg(long)]
    pub worktree: Option<PathBuf>,
    #[arg(long, value_enum)]
    pub model: Option<ModelArg>,
    #[arg(long = "reasoning-budget", value_enum)]
    pub reasoning_budget: Option<BudgetArg>,
}

pub fn run(db: &mut Database, repo_root: &Path, args: InteractiveArgs) -> Result<(), CliError> {
    if args.allocate {
        validate_handle(&args.handle)?;
        let worktree = args
            .worktree
            .as_ref()
            .ok_or_else(|| CliError::new(65, "--worktree is required when --allocate is set"))?;
        let worktree = canonicalize(worktree)?;
        if db.get_worktree(&worktree)?.is_none() {
            return Err(CliError::new(
                65,
                format!(
                    "Worktree {} not bootstrapped. Run 'agentctl bootstrap {}' first.",
                    worktree.display(),
                    worktree.display()
                ),
            ));
        }
        if db.get_agent(&args.handle)?.is_some() {
            return Err(CliError::new(
                65,
                format!("Handle {} already exists", args.handle),
            ));
        }
        let record = build_record(
            args.handle.clone(),
            worktree,
            None,
            args.model,
            args.reasoning_budget,
        );
        db.insert_agent(record)?;
    }

    let agent = db
        .get_agent(&args.handle)?
        .ok_or_else(|| CliError::new(65, format!("Unknown handle {}", args.handle)))?;
    if !agent.worktree_path.exists() {
        return Err(CliError::new(
            71,
            format!("Worktree {} is missing", agent.worktree_path.display()),
        ));
    }
    if db.get_active_turn(&agent.handle)?.is_some() {
        return Err(CliError::new(
            65,
            format!("Agent {} already has a running turn", agent.handle),
        ));
    }

    let resume_uuid = db.last_session_uuid(&agent.handle)?;
    let turn_dir = prepare_turn_dir(&agent, repo_root)?;
    let prompt_path = turn_dir.join("prompt.txt");
    fs::write(
        &prompt_path,
        format!("Interactive session started at {}\n", state::timestamp()),
    )
    .map_err(|err| CliError::new(70, format!("Failed to write prompt: {err}")))?;
    let log_path = turn_dir.join("events.jsonl");
    File::create(&log_path)
        .map_err(|err| CliError::new(70, format!("Failed to create log file: {err}")))?;
    let final_path = turn_dir.join("final_message.txt");
    File::create(&final_path)
        .map_err(|err| CliError::new(70, format!("Failed to create final message file: {err}")))?;

    let started_at = state::timestamp();
    let turn_id = db.create_turn(
        &agent.handle,
        &prompt_path,
        &log_path,
        &final_path,
        &turn_dir,
        &started_at,
    )?;

    let before_session = latest_history_session().ok().flatten();
    let mut child = spawn_tui(&agent, resume_uuid.clone())?;
    let pid = child.id() as i64;
    db.mark_turn_interactive(turn_id, resume_uuid.as_deref(), pid)?;
    println!(
        "Interactive Codex session for {} launched ({} mode).",
        agent.handle,
        if resume_uuid.is_some() {
            "resume"
        } else {
            "fresh"
        }
    );

    let status = child
        .wait()
        .map_err(|err| CliError::new(70, format!("Failed to wait for Codex: {err}")))?;

    let after_session = latest_history_session().ok().flatten();
    if let Some(new_id) = pick_new_session(before_session.as_deref(), after_session.as_deref()) {
        db.update_session_uuid(turn_id, &new_id)?;
    }

    if status.success() {
        db.mark_turn_stopped(turn_id, TurnStatus::Stopped, None)?;
        println!("Interactive session for {} ended.", agent.handle);
        Ok(())
    } else {
        db.mark_turn_failed(turn_id, "codex interactive exited with failure")?;
        Err(CliError::new(
            73,
            format!("Codex interactive exited with {}", status),
        ))
    }
}

fn spawn_tui(agent: &AgentRecord, resume_uuid: Option<String>) -> Result<Child, CliError> {
    let mut cmd = Command::new("codex");
    if let Some(uuid) = &resume_uuid {
        cmd.arg("resume").arg(uuid);
    }
    cmd.arg("--sandbox")
        .arg("danger-full-access")
        .arg("--ask-for-approval")
        .arg("never")
        .arg("-C")
        .arg(&agent.worktree_path)
        .arg("--model")
        .arg(agent.model.as_str())
        .stdin(Stdio::inherit())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .current_dir(&agent.worktree_path);

    cmd.env("AGENTCTL_HANDLE", &agent.handle);
    cmd.env("AGENTCTL_PARENT", &agent.parent_handle);
    cmd.env(
        "AGENTCTL_WORKTREE",
        agent.worktree_path.display().to_string(),
    );
    cmd.env("AGENTCTL_MODEL", agent.model.as_str());
    cmd.env("AGENTCTL_BUDGET", agent.reasoning_budget.as_str());

    cmd.spawn()
        .map_err(|err| CliError::new(73, format!("Failed to launch codex interactive: {err}")))
}

fn latest_history_session() -> Result<Option<String>, CliError> {
    let path = match history_path() {
        Some(path) => path,
        None => return Ok(None),
    };
    if !path.exists() {
        return Ok(None);
    }
    let file = File::open(&path)
        .map_err(|err| CliError::new(70, format!("Failed to open {}: {err}", path.display())))?;
    let reader = BufReader::new(file);
    let mut last: Option<String> = None;
    for line in reader.lines() {
        let line = match line {
            Ok(line) => line,
            Err(_) => continue,
        };
        if let Ok(entry) = serde_json::from_str::<HistoryEntry>(&line)
            && let Some(id) = entry.session_id
        {
            last = Some(id);
        }
    }
    Ok(last)
}

fn history_path() -> Option<PathBuf> {
    env::var("HOME")
        .ok()
        .map(PathBuf::from)
        .map(|home| home.join(".codex").join("history.jsonl"))
}

fn pick_new_session(before: Option<&str>, after: Option<&str>) -> Option<String> {
    after
        .filter(|latest| before != Some(*latest))
        .map(|value| value.to_string())
}

#[derive(Deserialize)]
struct HistoryEntry {
    session_id: Option<String>,
}
