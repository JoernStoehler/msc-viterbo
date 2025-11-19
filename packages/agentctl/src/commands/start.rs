use std::fs;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use clap::{ArgGroup, Args};

use crate::{
    error::CliError,
    state::{self, AgentRecord, Database},
};

use super::session::prepare_turn_dir;

#[derive(Args, Clone)]
#[command(group(
    ArgGroup::new("prompt_source")
        .required(true)
        .args(["prompt", "prompt_file"])
))]
pub struct StartArgs {
    pub handle: String,
    #[arg(long)]
    pub prompt: Option<String>,
    #[arg(long = "prompt-file")]
    pub prompt_file: Option<PathBuf>,
    #[arg(long, default_value_t = 30)]
    pub timeout: u64,
}

pub fn run(db: &mut Database, repo_root: &Path, args: StartArgs) -> Result<(), CliError> {
    let agent = db
        .get_agent(&args.handle)?
        .ok_or_else(|| CliError::new(65, format!("Unknown handle {}", args.handle)))?;
    if db.get_active_turn(&agent.handle)?.is_some() {
        return Err(CliError::new(
            65,
            format!("Agent {} already has a running turn", agent.handle),
        ));
    }
    if !agent.worktree_path.exists() {
        return Err(CliError::new(
            71,
            format!("Worktree {} is missing", agent.worktree_path.display()),
        ));
    }

    let resume_uuid = db.last_session_uuid(&agent.handle)?;
    let turn_dir = prepare_turn_dir(&agent, repo_root)?;
    let prompt_path = turn_dir.join("prompt.txt");
    match (args.prompt, args.prompt_file) {
        (Some(text), None) => fs::write(&prompt_path, text)
            .map_err(|err| CliError::new(70, format!("Failed to write prompt: {err}")))?,
        (None, Some(file)) => {
            fs::copy(&file, &prompt_path).map_err(|err| {
                CliError::new(
                    70,
                    format!("Failed to copy prompt file {}: {err}", file.display()),
                )
            })?;
        }
        _ => unreachable!("clap enforces prompt source"),
    }
    let log_path = turn_dir.join("events.jsonl");
    let final_path = turn_dir.join("final_message.txt");
    let started_at = state::timestamp();
    let turn_id = db.create_turn(
        &agent.handle,
        &prompt_path,
        &log_path,
        &final_path,
        &turn_dir,
        &started_at,
    )?;

    let mut child = spawn_exec_process(
        repo_root,
        &agent,
        turn_id,
        &prompt_path,
        &log_path,
        &final_path,
        resume_uuid.clone(),
    )?;

    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| CliError::new(70, "Exec process missing stdout".to_string()))?;
    let mut reader = BufReader::new(stdout);
    let mut line = String::new();
    let timeout = Duration::from_secs(args.timeout);
    let start = Instant::now();
    let mut session_uuid: Option<String> = None;
    loop {
        if start.elapsed() > timeout {
            child.kill().ok();
            db.mark_turn_failed(turn_id, "timeout waiting for session uuid")?;
            return Err(CliError::new(
                74,
                format!(
                    "Timed out waiting for Codex session UUID (>{}s)",
                    args.timeout
                ),
            ));
        }
        line.clear();
        let bytes = reader
            .read_line(&mut line)
            .map_err(|err| CliError::new(70, format!("Failed to read exec output: {err}")))?;
        if bytes == 0 {
            break;
        }
        if let Some(rest) = line.strip_prefix("SESSION ") {
            session_uuid = Some(rest.trim().to_string());
            break;
        } else if let Some(rest) = line.strip_prefix("ERROR ") {
            let msg = rest.trim().to_string();
            db.mark_turn_failed(turn_id, &msg)?;
            return Err(CliError::new(73, msg));
        }
    }

    let session_uuid = session_uuid.ok_or_else(|| {
        CliError::new(
            74,
            "Exec process exited before reporting a session UUID".to_string(),
        )
    })?;
    let pid = child.id() as i64;
    db.mark_turn_running(turn_id, &session_uuid, pid)?;
    println!(
        "started agent {}\nworktree: {}\nsession_uuid: {}\nmode: {}",
        agent.handle,
        agent.worktree_path.display(),
        session_uuid,
        if resume_uuid.is_some() {
            "resume"
        } else {
            "fresh"
        }
    );
    Ok(())
}

fn spawn_exec_process(
    repo_root: &Path,
    agent: &AgentRecord,
    turn_id: i64,
    prompt_path: &Path,
    log_path: &Path,
    final_path: &Path,
    resume_uuid: Option<String>,
) -> Result<Child, CliError> {
    let current_exe = std::env::current_exe()
        .map_err(|err| CliError::new(70, format!("Failed to locate agentctl binary: {err}")))?;
    let mut cmd = Command::new(current_exe);
    cmd.arg("_exec")
        .arg("--handle")
        .arg(&agent.handle)
        .arg("--turn-id")
        .arg(turn_id.to_string())
        .arg("--worktree")
        .arg(agent.worktree_path.display().to_string())
        .arg("--prompt-file")
        .arg(prompt_path.display().to_string())
        .arg("--log-path")
        .arg(log_path.display().to_string())
        .arg("--final-path")
        .arg(final_path.display().to_string())
        .arg("--repo-root")
        .arg(repo_root.display().to_string())
        .arg("--model")
        .arg(agent.model.as_str())
        .arg("--budget")
        .arg(agent.reasoning_budget.as_str())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit());

    if let Some(uuid) = &resume_uuid {
        cmd.arg("--resume-uuid").arg(uuid);
    }

    cmd.env("AGENTCTL_HANDLE", &agent.handle);
    cmd.env("AGENTCTL_PARENT", &agent.parent_handle);
    cmd.env(
        "AGENTCTL_WORKTREE",
        agent.worktree_path.display().to_string(),
    );
    cmd.env("AGENTCTL_MODEL", agent.model.as_str());
    cmd.env("AGENTCTL_BUDGET", agent.reasoning_budget.as_str());

    cmd.spawn()
        .map_err(|err| CliError::new(73, format!("Failed to spawn exec helper: {err}")))
}
