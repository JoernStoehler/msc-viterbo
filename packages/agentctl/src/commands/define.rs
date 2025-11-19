use std::env;
use std::path::PathBuf;

use clap::{Args, ValueEnum};

use crate::{
    error::CliError,
    state::{AgentModel, AgentRecord, Database, ReasoningBudget, timestamp},
    util::{canonicalize, validate_handle},
};

#[derive(Args, Clone)]
pub struct DefineArgs {
    pub handle: String,
    #[arg(long)]
    pub worktree: PathBuf,
    #[arg(long)]
    pub parent: Option<String>,
    #[arg(long, value_enum)]
    pub model: Option<ModelArg>,
    #[arg(long = "reasoning-budget", value_enum)]
    pub reasoning_budget: Option<BudgetArg>,
}

#[derive(Copy, Clone, ValueEnum)]
pub enum ModelArg {
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
pub enum BudgetArg {
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

pub fn run(db: &mut Database, args: DefineArgs) -> Result<(), CliError> {
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
    let record = build_record(
        args.handle,
        worktree,
        args.parent,
        args.model,
        args.reasoning_budget,
    );
    db.insert_agent(record)?;
    println!("Agent defined. Use 'agentctl start <handle> --prompt ...' to launch a turn.");
    Ok(())
}

pub fn build_record(
    handle: String,
    worktree: PathBuf,
    parent: Option<String>,
    model: Option<ModelArg>,
    budget: Option<BudgetArg>,
) -> AgentRecord {
    let parent_handle = parent
        .or_else(|| env::var("AGENTCTL_HANDLE").ok())
        .unwrap_or_else(|| "project_owner".into());
    let model = model.map(AgentModel::from).unwrap_or(AgentModel::Gpt5Codex);
    let reasoning_budget = budget
        .map(ReasoningBudget::from)
        .unwrap_or(ReasoningBudget::High);

    AgentRecord {
        handle,
        worktree_path: worktree,
        parent_handle,
        model,
        reasoning_budget,
        defined_at: timestamp(),
    }
}
