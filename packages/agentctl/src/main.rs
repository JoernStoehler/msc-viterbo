mod error;
mod state;
mod util;

use std::env;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::time::{Duration, Instant};

use clap::{ArgGroup, Parser, Subcommand, ValueEnum};
use serde::Deserialize;

use crate::error::CliError;
use crate::state::{
    AgentModel, AgentRecord, AgentWithStatus, Database, ReasoningBudget, TurnStatus,
};
use crate::util::{
    canonicalize, ensure_repo_root, format_table, git_current_branch, validate_handle,
};

#[derive(Parser)]
#[command(
    name = "agentctl",
    author,
    version,
    about = "Orchestrator for thesis agents"
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    List {
        #[arg(long)]
        json: bool,
    },
    Bootstrap {
        worktree: PathBuf,
    },
    Define(DefineArgs),
    Start(StartArgs),
    Stop {
        handle: String,
    },
    Await(AwaitArgs),
    Print(PrintArgs),
    #[command(name = "self")]
    SelfCmd {
        #[arg(long)]
        json: bool,
    },
    #[command(name = "_exec", hide = true)]
    Exec(ExecArgs),
}

#[derive(Parser)]
struct DefineArgs {
    handle: String,
    #[arg(long)]
    worktree: PathBuf,
    #[arg(long)]
    parent: Option<String>,
    #[arg(long, value_enum)]
    model: Option<ModelArg>,
    #[arg(long = "reasoning-budget", value_enum)]
    reasoning_budget: Option<BudgetArg>,
}

#[derive(Parser)]
#[command(group(
    ArgGroup::new("prompt_source")
        .required(true)
        .args(["prompt", "prompt_file"])
))]
struct StartArgs {
    handle: String,
    #[arg(long)]
    prompt: Option<String>,
    #[arg(long = "prompt-file")]
    prompt_file: Option<PathBuf>,
    #[arg(long, default_value_t = 30)]
    timeout: u64,
}

#[derive(Parser)]
struct AwaitArgs {
    handle: String,
    #[arg(long)]
    timeout: Option<u64>,
}

#[derive(Parser)]
struct PrintArgs {
    handle: String,
    #[arg(long = "last", default_value_t = 1)]
    last: u32,
    #[arg(long)]
    json: bool,
}

#[derive(Parser)]
struct ExecArgs {
    #[arg(long)]
    handle: String,
    #[arg(long = "turn-id")]
    turn_id: i64,
    #[arg(long)]
    worktree: PathBuf,
    #[arg(long = "prompt-file")]
    prompt_file: PathBuf,
    #[arg(long = "log-path")]
    log_path: PathBuf,
    #[arg(long = "final-path")]
    final_path: PathBuf,
    #[arg(long = "repo-root")]
    repo_root: PathBuf,
    #[arg(long = "model")]
    model: String,
    #[arg(long = "budget")]
    budget: String,
    #[arg(long = "resume-uuid")]
    resume_uuid: Option<String>,
}

#[derive(Copy, Clone, ValueEnum)]
enum ModelArg {
    #[value(name = "gpt-5")]
    Gpt5,
    #[value(name = "gpt-5-codex")]
    Gpt5Codex,
}

impl From<ModelArg> for AgentModel {
    fn from(value: ModelArg) -> Self {
        match value {
            ModelArg::Gpt5 => AgentModel::Gpt5,
            ModelArg::Gpt5Codex => AgentModel::Gpt5Codex,
        }
    }
}

#[derive(Copy, Clone, ValueEnum)]
enum BudgetArg {
    High,
    Medium,
    Low,
}

impl From<BudgetArg> for ReasoningBudget {
    fn from(value: BudgetArg) -> Self {
        match value {
            BudgetArg::High => ReasoningBudget::High,
            BudgetArg::Medium => ReasoningBudget::Medium,
            BudgetArg::Low => ReasoningBudget::Low,
        }
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("Error: {}", err);
            ExitCode::from(err.exit_code())
        }
    }
}

fn run() -> Result<(), CliError> {
    let cli = Cli::parse();
    // `_exec` receives the repo root as argument because it may be spawned before `cd`.
    if let Commands::Exec(args) = cli.command {
        return cmd_exec(args);
    }

    let repo_root = ensure_repo_root()?;
    let mut db = Database::open(&repo_root)?;

    match cli.command {
        Commands::List { json } => cmd_list(&mut db, json),
        Commands::Bootstrap { worktree } => cmd_bootstrap(&mut db, &repo_root, worktree),
        Commands::Define(args) => cmd_define(&mut db, args),
        Commands::Start(args) => cmd_start(&mut db, &repo_root, args),
        Commands::Stop { handle } => cmd_stop(&mut db, handle),
        Commands::Await(args) => cmd_await(&mut db, args),
        Commands::Print(args) => cmd_print(&mut db, args),
        Commands::SelfCmd { json } => cmd_self(&mut db, json),
        Commands::Exec(_) => unreachable!(),
    }
}

fn cmd_list(db: &mut Database, json: bool) -> Result<(), CliError> {
    let rows = db.list_agents_with_status()?;
    if json {
        println!(
            "{}",
            serde_json::to_string_pretty(&rows).map_err(|err| CliError::new(1, err.to_string()))?
        );
        return Ok(());
    }

    let mut table = Vec::with_capacity(rows.len() + 1);
    table.push(vec![
        "handle".into(),
        "worktree".into(),
        "parent".into(),
        "model".into(),
        "budget".into(),
        "status".into(),
        "last_active".into(),
    ]);
    for AgentWithStatus {
        agent,
        status,
        last_active,
    } in rows
    {
        table.push(vec![
            agent.handle.clone(),
            agent.worktree_path.display().to_string(),
            agent.parent_handle.clone(),
            agent.model.as_str().to_string(),
            agent.reasoning_budget.as_str().to_string(),
            status
                .map(|s| s.as_str().to_string())
                .unwrap_or_else(|| "idle".into()),
            last_active.unwrap_or_else(|| agent.defined_at.clone()),
        ]);
    }
    println!("{}", format_table(&table));
    Ok(())
}

fn cmd_bootstrap(db: &mut Database, repo_root: &Path, worktree: PathBuf) -> Result<(), CliError> {
    let path = canonicalize(&worktree)?;
    if !path.exists() {
        return Err(CliError::new(
            65,
            format!("Worktree {} does not exist", path.display()),
        ));
    }
    if !path.starts_with(repo_root) {
        return Err(CliError::new(
            65,
            format!(
                "Worktree {} is outside repo {}",
                path.display(),
                repo_root.display()
            ),
        ));
    }
    let branch = git_current_branch(&path)?;
    db.upsert_worktree(&path, &branch, repo_root)?;
    run_bootstrap_hook(repo_root, &path, &branch)?;
    println!(
        "Bootstrapped worktree {} (branch {})",
        path.display(),
        branch
    );
    Ok(())
}

fn cmd_define(db: &mut Database, args: DefineArgs) -> Result<(), CliError> {
    validate_handle(&args.handle)?;
    let worktree = canonicalize(&args.worktree)?;
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
    let parent = args
        .parent
        .or_else(|| env::var("AGENTCTL_HANDLE").ok())
        .unwrap_or_else(|| "project_owner".into());
    let model = args
        .model
        .map(AgentModel::from)
        .unwrap_or(AgentModel::Gpt5Codex);
    let budget = args
        .reasoning_budget
        .map(ReasoningBudget::from)
        .unwrap_or(ReasoningBudget::High);

    let record = AgentRecord {
        handle: args.handle,
        worktree_path: worktree,
        parent_handle: parent,
        model,
        reasoning_budget: budget,
        defined_at: state::timestamp(),
    };
    db.insert_agent(record)?;
    println!("Agent defined. Use 'agentctl start <handle> --prompt ...' to launch a turn.");
    Ok(())
}

fn cmd_start(db: &mut Database, repo_root: &Path, args: StartArgs) -> Result<(), CliError> {
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
    drop(reader);

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

fn cmd_stop(db: &mut Database, handle: String) -> Result<(), CliError> {
    let turn = db
        .get_active_turn(&handle)?
        .ok_or_else(|| CliError::new(65, format!("No running turn for {}", handle)))?;
    let pid = turn
        .child_pid
        .ok_or_else(|| CliError::new(65, "Turn has no recorded exec pid".to_string()))?;
    terminate_pid(pid, true)?;
    db.mark_turn_stopped(turn.id, TurnStatus::Stopped, Some("stopped via agentctl"))?;
    println!("Stopped agent {}.", handle);
    Ok(())
}

fn cmd_await(db: &mut Database, args: AwaitArgs) -> Result<(), CliError> {
    let turn = db
        .get_active_turn(&args.handle)?
        .ok_or_else(|| CliError::new(65, format!("No running turn for {}", args.handle)))?;
    if let Some(pid) = turn.child_pid {
        wait_for_pid(pid, args.timeout)?;
    }
    println!("Agent {} completed.", args.handle);
    Ok(())
}

fn cmd_print(db: &mut Database, args: PrintArgs) -> Result<(), CliError> {
    let turns = db.list_recent_turns(&args.handle, args.last as i64)?;
    if args.json {
        println!(
            "{}",
            serde_json::to_string_pretty(&turns)
                .map_err(|err| CliError::new(1, err.to_string()))?
        );
        return Ok(());
    }
    for turn in turns {
        println!("Turn {} ({})", turn.id, turn.status.as_str());
        println!("started: {}", turn.started_at);
        if let Some(stopped) = &turn.stopped_at {
            println!("stopped: {}", stopped);
        }
        if let Some(uuid) = &turn.session_uuid {
            println!("session_uuid: {}", uuid);
        }
        println!("prompt:");
        print_file(&turn.prompt_path)?;
        println!("final message:");
        if turn.final_path.exists() {
            print_file(&turn.final_path)?;
        } else {
            println!("[no final message yet]");
        }
        println!();
    }
    Ok(())
}

fn cmd_self(db: &mut Database, json: bool) -> Result<(), CliError> {
    let handle = match env::var("AGENTCTL_HANDLE") {
        Ok(handle) => handle,
        Err(_) => {
            let cwd = env::current_dir()
                .map_err(|err| CliError::new(65, format!("Unable to read current dir: {err}")))?;
            let path = canonicalize(&cwd)?;
            let matches = db.agents_for_worktree(&path)?;
            if matches.len() != 1 {
                return Err(CliError::new(
                    64,
                    "Set AGENTCTL_HANDLE or run inside a worktree with a single agent.".to_string(),
                ));
            }
            matches.into_iter().next().unwrap().handle
        }
    };
    let record = db
        .get_agent(&handle)?
        .ok_or_else(|| CliError::new(65, format!("Unknown handle {}", handle)))?;
    if json {
        println!(
            "{}",
            serde_json::to_string_pretty(&record)
                .map_err(|err| CliError::new(1, err.to_string()))?
        );
    } else {
        println!("handle: {}", record.handle);
        println!("worktree: {}", record.worktree_path.display());
        println!("parent: {}", record.parent_handle);
        println!("model: {}", record.model.as_str());
        println!("budget: {}", record.reasoning_budget.as_str());
        println!("defined_at: {}", record.defined_at);
    }
    Ok(())
}

fn cmd_exec(args: ExecArgs) -> Result<(), CliError> {
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

    let stdout = child.stdout.take().unwrap();
    let stderr = child.stderr.take().unwrap();
    let stderr_path = args.log_path.clone();
    std::thread::spawn(move || {
        let reader = BufReader::new(stderr).lines();
        if let Ok(mut file) = File::options().create(true).append(true).open(&stderr_path) {
            for line in reader.flatten() {
                let _ = writeln!(file, "STDERR {}", line);
            }
        }
    });

    let expected_uuid = args.resume_uuid.clone();
    let mut reader = BufReader::new(stdout);
    let mut line = String::new();
    let mut session_uuid: Option<String> = None;

    while reader
        .read_line(&mut line)
        .map_err(|err| CliError::new(70, format!("Failed to read codex output: {err}")))?
        > 0
    {
        let trimmed = line.trim_end();
        writeln!(log_file, "{trimmed}").ok();
        if session_uuid.is_none() {
            if let Some(uuid) = extract_session_id(trimmed) {
                if let Some(expected) = &expected_uuid {
                    if uuid != *expected {
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
                }
                session_uuid = Some(uuid.clone());
                println!("SESSION {uuid}");
                std::io::stdout().flush().ok();
            }
        }
        line.clear();
    }

    if session_uuid.is_none() {
        println!("ERROR session-id-missing");
        db.mark_turn_failed(args.turn_id, "session uuid missing")?;
        return Err(CliError::new(74, "Session UUID missing".to_string()));
    }

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

fn prepare_turn_dir(agent: &AgentRecord, repo_root: &Path) -> Result<PathBuf, CliError> {
    let base = util::sessions_root(repo_root)?
        .join("sessions")
        .join(&agent.handle);
    fs::create_dir_all(&base)
        .map_err(|err| CliError::new(70, format!("Failed to create {}: {err}", base.display())))?;
    let timestamp = state::timestamp().replace(':', "-");
    let dir = base.join(format!("turn-{}", timestamp));
    fs::create_dir_all(&dir)
        .map_err(|err| CliError::new(70, format!("Failed to create {}: {err}", dir.display())))?;
    Ok(dir)
}

fn spawn_exec_process(
    repo_root: &Path,
    agent: &AgentRecord,
    turn_id: i64,
    prompt_path: &Path,
    log_path: &Path,
    final_path: &Path,
    resume_uuid: Option<String>,
) -> Result<std::process::Child, CliError> {
    let current_exe = env::current_exe()
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

fn terminate_pid(pid: i64, wait: bool) -> Result<(), CliError> {
    use nix::sys::signal::{Signal, kill};
    use nix::unistd::Pid;

    let target = Pid::from_raw(pid as i32);
    match kill(target, Signal::SIGTERM) {
        Ok(_) => {}
        Err(nix::errno::Errno::ESRCH) => return Ok(()),
        Err(err) => {
            return Err(CliError::new(
                70,
                format!("Failed to signal process: {err}"),
            ));
        }
    }
    if wait {
        wait_for_pid(pid, Some(10))?;
    }
    Ok(())
}

fn wait_for_pid(pid: i64, timeout_secs: Option<u64>) -> Result<(), CliError> {
    let timeout = timeout_secs.unwrap_or(0);
    let start = Instant::now();
    loop {
        if !process_alive(pid) {
            return Ok(());
        }
        if timeout > 0 && start.elapsed() > Duration::from_secs(timeout) {
            return Err(CliError::new(
                124,
                format!("Process {pid} did not exit within {timeout}s"),
            ));
        }
        std::thread::sleep(Duration::from_millis(250));
    }
}

fn process_alive(pid: i64) -> bool {
    let rc = unsafe { nix::libc::kill(pid as nix::libc::pid_t, 0) };
    if rc == 0 {
        true
    } else {
        nix::errno::Errno::last_raw() != nix::libc::ESRCH
    }
}

fn print_file(path: &Path) -> Result<(), CliError> {
    match fs::read_to_string(path) {
        Ok(content) => println!("{content}"),
        Err(err) => println!("(unable to read {}: {err})", path.display()),
    }
    Ok(())
}
fn run_bootstrap_hook(repo_root: &Path, worktree: &Path, branch: &str) -> Result<(), CliError> {
    let hook = match env::var("AGENTCTL_BOOTSTRAP_HOOK") {
        Ok(value) if !value.trim().is_empty() => value,
        _ => return Ok(()),
    };
    let status = Command::new("bash")
        .arg("-lc")
        .arg(hook)
        .current_dir(repo_root)
        .env("AGENTCTL_REPO_ROOT", repo_root.display().to_string())
        .env("AGENTCTL_WORKTREE", worktree.display().to_string())
        .env("AGENTCTL_WORKTREE_BRANCH", branch)
        .status()
        .map_err(|err| CliError::new(70, format!("Bootstrap hook failed to start: {err}")))?;
    if !status.success() {
        return Err(CliError::new(
            70,
            format!("Bootstrap hook exited with {}", status),
        ));
    }
    Ok(())
}
