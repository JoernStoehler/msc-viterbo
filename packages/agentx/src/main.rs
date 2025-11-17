use std::env;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, Context, Result};
use chrono::{DateTime, Utc};
use clap::{Parser, Subcommand};
use serde::{Deserialize, Serialize};

const PROJECT_ID: &str = "msc-viterbo";

#[derive(Parser)]
#[command(name = "agentx")]
#[command(about = "Agent tooling for the msc-viterbo project", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Manage agents (list, start, etc.).
    Agent {
        #[command(subcommand)]
        command: AgentCommands,
    },
    /// Manage worktrees for this project.
    Worktree {
        #[command(subcommand)]
        command: WorktreeCommands,
    },
}

#[derive(Subcommand)]
enum AgentCommands {
    /// List known agents, optionally filtered.
    List {
        /// Simple filters of the form key=value (e.g. status=active).
        #[arg(long)]
        filter: Vec<String>,
    },
    /// Record a new agent in the database (stub; does not start processes yet).
    Start {
        /// Agent identifier (e.g. codex-cli session name).
        #[arg(long)]
        id: String,
        /// Name of the worktree this agent is associated with.
        #[arg(long)]
        worktree: Option<String>,
    },
}

#[derive(Subcommand)]
enum WorktreeCommands {
    /// Create a new worktree for a focused task or experiment.
    Create {
        /// Source branch or ref to branch from (default: main).
        #[arg(long, default_value = "main")]
        source: String,
        /// Logical worktree name / slug (e.g. issue-0018-fix-typos-in-readme).
        #[arg(long)]
        name: Option<String>,
        /// Explicit worktree path (overrides name and default root).
        #[arg(long)]
        target: Option<PathBuf>,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct AgentRecord {
    id: String,
    status: String,
    worktree: Option<String>,
    created_at: DateTime<Utc>,
    last_seen: Option<DateTime<Utc>>,
}

#[derive(Debug, Default, Serialize, Deserialize)]
struct AgentDatabase {
    agents: Vec<AgentRecord>,
}

impl AgentDatabase {
    fn load(path: &Path) -> Result<Self> {
        if !path.exists() {
            return Ok(Self::default());
        }
        let data = fs::read_to_string(path)
            .with_context(|| format!("reading agent database at {}", path.display()))?;
        let db: Self = serde_json::from_str(&data)
            .with_context(|| "parsing agent database JSON".to_string())?;
        Ok(db)
    }

    fn save(&self, path: &Path) -> Result<()> {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .with_context(|| format!("creating database directory {}", parent.display()))?;
        }
        let json =
            serde_json::to_string_pretty(self).with_context(|| "serialising agent database")?;
        let mut tmp = path.to_path_buf();
        tmp.set_extension("json.tmp");
        {
            let mut f = fs::File::create(&tmp)
                .with_context(|| format!("creating temp database file {}", tmp.display()))?;
            f.write_all(json.as_bytes())
                .with_context(|| format!("writing temp database file {}", tmp.display()))?;
            f.flush().ok();
        }
        fs::rename(&tmp, path)
            .with_context(|| format!("replacing database file {}", path.display()))?;
        Ok(())
    }

    fn list_filtered(&self, filters: &[FilterExpr]) -> Vec<&AgentRecord> {
        self.agents
            .iter()
            .filter(|a| filters.iter().all(|f| f.matches(a)))
            .collect()
    }

    fn add_agent(&mut self, record: AgentRecord) {
        self.agents.retain(|a| a.id != record.id);
        self.agents.push(record);
    }
}

#[derive(Debug, Clone)]
struct FilterExpr {
    key: String,
    value: String,
}

impl FilterExpr {
    fn parse(s: &str) -> Option<Self> {
        let (k, v) = s.split_once('=')?;
        if k.is_empty() || v.is_empty() {
            return None;
        }
        Some(Self {
            key: k.to_string(),
            value: v.to_string(),
        })
    }

    fn matches(&self, agent: &AgentRecord) -> bool {
        match self.key.as_str() {
            "id" => agent.id == self.value,
            "status" => agent.status == self.value,
            "worktree" => agent.worktree.as_deref() == Some(self.value.as_str()),
            _ => true,
        }
    }
}

fn agentx_root() -> Result<PathBuf> {
    let home = env::var("HOME").context("HOME not set")?;
    Ok(Path::new(&home).join(".agentx").join(PROJECT_ID))
}

fn agentx_db_path() -> Result<PathBuf> {
    Ok(agentx_root()?.join("database.json"))
}

fn worktrees_root() -> PathBuf {
    if let Ok(p) = env::var("AGENTX_WORKTREES_DIR") {
        PathBuf::from(p)
    } else {
        PathBuf::from("/var/tmp/msc-viterbo/worktrees")
    }
}

fn repo_root() -> Result<PathBuf> {
    let output = Command::new("git")
        .args(["rev-parse", "--show-toplevel"])
        .output()
        .context("running git rev-parse --show-toplevel")?;
    if !output.status.success() {
        return Err(anyhow!("not inside a git repository"));
    }
    let s = String::from_utf8_lossy(&output.stdout).trim().to_string();
    Ok(PathBuf::from(s))
}

fn run_git(args: &[&str], cwd: &Path) -> Result<()> {
    let status = Command::new("git")
        .args(args)
        .current_dir(cwd)
        .status()
        .with_context(|| format!("running git {}", args.join(" ")))?;
    if !status.success() {
        return Err(anyhow!("git command failed: {}", args.join(" ")));
    }
    Ok(())
}

fn cmd_agent_list(filter: Vec<String>) -> Result<()> {
    let filters: Vec<FilterExpr> = filter.iter().filter_map(|s| FilterExpr::parse(s)).collect();

    let db_path = agentx_db_path()?;
    let db = AgentDatabase::load(&db_path)?;
    let agents = db.list_filtered(&filters);

    for a in agents {
        println!(
            "id={}\tstatus={}\tworktree={}",
            a.id,
            a.status,
            a.worktree.as_deref().unwrap_or("")
        );
    }

    Ok(())
}

fn cmd_agent_start(id: String, worktree: Option<String>) -> Result<()> {
    let db_path = agentx_db_path()?;
    let mut db = AgentDatabase::load(&db_path)?;

    let now = Utc::now();
    let record = AgentRecord {
        id,
        status: "starting".to_string(),
        worktree,
        created_at: now,
        last_seen: Some(now),
    };

    db.add_agent(record);
    db.save(&db_path)?;

    println!("Recorded agent in database (note: process startup is not automated yet).");
    Ok(())
}

fn cmd_worktree_create(
    source: String,
    name: Option<String>,
    target: Option<PathBuf>,
) -> Result<()> {
    let repo = repo_root()?;
    let root = worktrees_root();

    fs::create_dir_all(&root)
        .with_context(|| format!("creating worktrees root at {}", root.display()))?;

    let worktree_path = if let Some(t) = target {
        t
    } else {
        let name = name.ok_or_else(|| anyhow!("either --name or --target must be provided"))?;
        root.join(name)
    };

    if worktree_path.exists() {
        return Err(anyhow!(
            "worktree target already exists: {}",
            worktree_path.display()
        ));
    }

    let slug = worktree_path
        .file_name()
        .and_then(|s| s.to_str())
        .ok_or_else(|| anyhow!("could not derive worktree slug from target path"))?;
    let branch_name = format!("agentx/{}", slug);

    // Create branch if needed
    let show_ref = Command::new("git")
        .args([
            "show-ref",
            "--verify",
            "--quiet",
            &format!("refs/heads/{}", branch_name),
        ])
        .current_dir(&repo)
        .status()
        .context("checking for existing branch")?;

    if !show_ref.success() {
        // Prefer origin/<source> if it exists
        let origin_ref = format!("origin/{}", source);
        let base_ref = Command::new("git")
            .args([
                "show-ref",
                "--verify",
                "--quiet",
                &format!("refs/remotes/{}", origin_ref),
            ])
            .current_dir(&repo)
            .status()
            .ok()
            .filter(|s| s.success())
            .map(|_| origin_ref.clone())
            .unwrap_or_else(|| source.clone());

        run_git(&["branch", &branch_name, &base_ref], &repo)?;
    }

    // Add the worktree
    run_git(
        &[
            "worktree",
            "add",
            worktree_path
                .to_str()
                .ok_or_else(|| anyhow!("non-UTF8 worktree path"))?,
            &branch_name,
        ],
        &repo,
    )?;

    // Ensure /workspaces/worktrees symlink is in place (best-effort).
    if let Ok(workspaces) = env::var("WORKSPACES_ROOT") {
        let ws_root = Path::new(&workspaces).join("worktrees");
        if !ws_root.exists() {
            let _ = fs::create_dir_all(&ws_root);
        }
    }

    println!(
        "Created worktree at {} on branch {}",
        worktree_path.display(),
        branch_name
    );
    Ok(())
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Agent { command } => match command {
            AgentCommands::List { filter } => cmd_agent_list(filter),
            AgentCommands::Start { id, worktree } => cmd_agent_start(id, worktree),
        },
        Commands::Worktree { command } => match command {
            WorktreeCommands::Create {
                source,
                name,
                target,
            } => cmd_worktree_create(source, name, target),
        },
    }
}
