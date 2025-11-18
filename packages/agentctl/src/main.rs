use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Args, Parser, Subcommand};
use rand::seq::SliceRandom;
use rand::{Rng, thread_rng};

#[derive(Parser)]
#[command(
    name = "agentctl",
    about = "Minimal controller for thesis agents",
    version
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    Provision(ProvisionArgs),
    Start(StartArgs),
    List,
    Stop(StopArgs),
    Resume(ResumeArgs),
    Merge(MergeArgs),
    Remove(RemoveArgs),
}

#[derive(Args)]
struct ProvisionArgs {
    /// Destination worktree path
    worktree: PathBuf,
    /// Feature branch to create
    #[arg(long)]
    branch: String,
    /// Source branch for the new worktree
    #[arg(long = "from-branch")]
    from_branch: Option<String>,
}

#[derive(Args)]
struct StartArgs {
    /// Existing worktree path
    worktree: PathBuf,
    /// Prompt text passed to the orchestrator
    #[arg(long)]
    prompt: String,
}

#[derive(Args)]
struct StopArgs {
    /// Agent session identifier
    uuid: String,
}

#[derive(Args)]
struct ResumeArgs {
    /// Agent session identifier
    uuid: String,
    /// Prompt file consumed by the orchestrator
    #[arg(long = "prompt-file")]
    prompt_file: PathBuf,
}

#[derive(Args)]
struct MergeArgs {
    /// Source worktree path
    source: PathBuf,
    /// Target worktree path
    #[arg(long = "into")]
    target: PathBuf,
    #[arg(long = "ignore-uncomitted-source")]
    ignore_uncomitted_source: bool,
    #[arg(long = "allow-uncomitted-target")]
    allow_uncomitted_target: bool,
    #[arg(long = "attempt-rebase")]
    attempt_rebase: bool,
    #[arg(long = "attempt-squash")]
    attempt_squash: bool,
    #[arg(long = "ignore-missing-squash")]
    ignore_missing_squash: bool,
    #[arg(long = "allow-merge-conflict")]
    allow_merge_conflict: bool,
}

#[derive(Args)]
struct RemoveArgs {
    /// Worktree path to remove
    worktree: PathBuf,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let mut rng = thread_rng();

    let code = match cli.command {
        Command::Provision(args) => handle_provision(args),
        Command::Start(args) => handle_start(args, &mut rng),
        Command::List => handle_list(&mut rng),
        Command::Stop(args) => handle_stop(args, &mut rng),
        Command::Resume(args) => handle_resume(args, &mut rng),
        Command::Merge(args) => handle_merge(args, &mut rng),
        Command::Remove(args) => handle_remove(args, &mut rng),
    };

    code
}

fn handle_provision(args: ProvisionArgs) -> ExitCode {
    let parent = args.from_branch.as_deref().unwrap_or("main");
    println!(
        "Worktree is ready. Start a new agent with 'agentctl start {} --prompt \"...\"' (branch {} from {})",
        args.worktree.display(),
        args.branch,
        parent
    );
    ExitCode::SUCCESS
}

fn handle_start(_args: StartArgs, rng: &mut impl Rng) -> ExitCode {
    println!("{}", random_agent_id(rng));
    ExitCode::SUCCESS
}

fn handle_list(rng: &mut impl Rng) -> ExitCode {
    let mut rows = preset_rows();
    if rng.gen_bool(0.4) {
        rows.push(random_row(rng));
    }
    rows.shuffle(rng);
    let display_count = rng.gen_range(2..=rows.len());

    println!("uuid status worktree updated_at");
    for row in rows.into_iter().take(display_count) {
        println!(
            "{} {} {} {}",
            row.uuid, row.status, row.worktree, row.updated_at
        );
    }

    ExitCode::SUCCESS
}

fn handle_stop(args: StopArgs, rng: &mut impl Rng) -> ExitCode {
    let uuid = args.uuid;
    match rng.gen_range(0..3) {
        0 => {
            println!("Stopped agent {}", uuid);
            ExitCode::SUCCESS
        }
        1 => {
            eprintln!("Error: Unknown agent {}", uuid);
            ExitCode::from(1)
        }
        _ => {
            eprintln!("Error: Agent already stopped {}", uuid);
            ExitCode::from(2)
        }
    }
}

fn handle_resume(args: ResumeArgs, rng: &mut impl Rng) -> ExitCode {
    let uuid = args.uuid;
    let prompt_file = args.prompt_file;
    match rng.gen_range(0..4) {
        0 => {
            println!("Resumed agent {} with {}", uuid, prompt_file.display());
            ExitCode::SUCCESS
        }
        1 => {
            eprintln!("Error: Unknown agent {}", uuid);
            ExitCode::from(3)
        }
        2 => {
            eprintln!(
                "Error: Agent already running {} {}",
                uuid,
                sample_worktree()
            );
            ExitCode::from(4)
        }
        _ => {
            eprintln!(
                "Error: Worktree no longer present {} {}",
                uuid,
                sample_worktree()
            );
            ExitCode::from(5)
        }
    }
}

fn handle_merge(args: MergeArgs, rng: &mut impl Rng) -> ExitCode {
    let enabled_flags = args.enabled_flags();
    match rng.gen_range(0..4) {
        0 => {
            println!("Merge successful.");
            if !enabled_flags.is_empty() {
                println!("Applied flags: {}", enabled_flags.join(", "));
            }
            ExitCode::SUCCESS
        }
        1 => {
            eprintln!(
                "validation failed: uncommitted changes in source folder, \
uncommitted changes in target folder, need to rebase before merge, need to squash before merge, will cause merge conflicts\n\
Flags to proceed regardless: --ignore-uncomitted-source, --allow-uncomitted-target, --attempt-rebase, --attempt-squash / --ignore-missing-squash, --allow-merge-conflict"
            );
            ExitCode::from(10)
        }
        2 => {
            eprintln!(
                "Merge conflicts occured, please fix manually in target directory {}.",
                args.target.display()
            );
            ExitCode::from(11)
        }
        _ => {
            eprintln!(
                "Rebase conflicts occured, please fix manually in source directory {}.",
                args.source.display()
            );
            ExitCode::from(12)
        }
    }
}

fn handle_remove(args: RemoveArgs, rng: &mut impl Rng) -> ExitCode {
    let worktree = args.worktree;
    if rng.gen_bool(0.5) {
        println!(
            "Removed unused worktree {}. Archived agents: {}",
            worktree.display(),
            random_agent_list(rng)
        );
        ExitCode::SUCCESS
    } else {
        eprintln!(
            "Cannot remove worktree {} while agents are running in it: {}",
            worktree.display(),
            random_agent_list(rng)
        );
        ExitCode::from(20)
    }
}

#[derive(Clone)]
struct AgentRow {
    uuid: String,
    status: String,
    worktree: String,
    updated_at: String,
}

fn preset_rows() -> Vec<AgentRow> {
    const ROWS: &[(&str, &str, &str, &str)] = &[
        (
            "8f12-873c",
            "running",
            "/workspaces/worktrees/issue-123",
            "2025-11-18T12:35:14",
        ),
        (
            "9acb-1234",
            "stopped",
            "/workspaces/worktrees/issue-120",
            "2025-11-18T10:24:10",
        ),
        (
            "04c0-ffde",
            "running",
            "/workspaces/worktrees/issue-140",
            "2025-11-18T11:02:01",
        ),
    ];

    ROWS.iter()
        .map(|(uuid, status, worktree, updated)| AgentRow {
            uuid: (*uuid).into(),
            status: (*status).into(),
            worktree: (*worktree).into(),
            updated_at: (*updated).into(),
        })
        .collect()
}

fn random_row(rng: &mut impl Rng) -> AgentRow {
    let issue: u16 = rng.gen_range(200..400);
    AgentRow {
        uuid: random_agent_id(rng),
        status: ["running", "stopped", "booting"]
            .choose(rng)
            .unwrap()
            .to_string(),
        worktree: format!("/workspaces/worktrees/issue-{}", issue),
        updated_at: random_timestamp(rng),
    }
}

fn random_agent_list(rng: &mut impl Rng) -> String {
    let mut ids = vec!["8f12-873c", "9acb-1234", "5d77-00aa", "0042-1337"];
    ids.shuffle(rng);
    let count = rng.gen_range(1..=ids.len());
    format!("[{}]", ids[..count].join(", "))
}

fn random_timestamp(rng: &mut impl Rng) -> String {
    format!(
        "2025-11-18T{:02}:{:02}:{:02}",
        rng.gen_range(0..24),
        rng.gen_range(0..60),
        rng.gen_range(0..60)
    )
}

fn random_agent_id(rng: &mut impl Rng) -> String {
    format!(
        "{:04x}-{:04x}",
        rng.gen_range(0u16..=0xFFFF),
        rng.gen_range(0u16..=0xFFFF)
    )
}

fn sample_worktree() -> &'static str {
    "/workspaces/worktrees/issue-123"
}

impl MergeArgs {
    fn enabled_flags(&self) -> Vec<&'static str> {
        let mut flags = Vec::new();
        if self.ignore_uncomitted_source {
            flags.push("--ignore-uncomitted-source");
        }
        if self.allow_uncomitted_target {
            flags.push("--allow-uncomitted-target");
        }
        if self.attempt_rebase {
            flags.push("--attempt-rebase");
        }
        if self.attempt_squash {
            flags.push("--attempt-squash");
        }
        if self.ignore_missing_squash {
            flags.push("--ignore-missing-squash");
        }
        if self.allow_merge_conflict {
            flags.push("--allow-merge-conflict");
        }
        flags
    }
}
