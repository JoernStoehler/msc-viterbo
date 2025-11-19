use std::path::PathBuf;

use serde::Serialize;

#[derive(Debug, Clone, Serialize)]
pub struct WorktreeRecord {
    pub path: PathBuf,
    pub branch: String,
    pub repo_root: PathBuf,
    pub bootstrapped_at: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct AgentRecord {
    pub handle: String,
    pub worktree_path: PathBuf,
    pub parent_handle: String,
    pub model: AgentModel,
    pub reasoning_budget: ReasoningBudget,
    pub defined_at: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct AgentWithStatus {
    pub agent: AgentRecord,
    pub status: Option<TurnStatus>,
    pub last_active: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct TurnRecord {
    pub id: i64,
    pub handle: String,
    pub turn_number: i64,
    pub status: TurnStatus,
    pub prompt_path: PathBuf,
    pub log_path: PathBuf,
    pub final_path: PathBuf,
    pub turn_dir: PathBuf,
    pub session_uuid: Option<String>,
    pub child_pid: Option<i64>,
    pub started_at: String,
    pub last_active_at: String,
    pub stopped_at: Option<String>,
    pub failure_reason: Option<String>,
}

#[derive(Debug, Clone, Copy, Serialize, PartialEq, Eq)]
pub enum AgentModel {
    #[serde(rename = "gpt-5")]
    Gpt5,
    #[serde(rename = "gpt-5-codex")]
    Gpt5Codex,
}

impl AgentModel {
    pub fn as_str(self) -> &'static str {
        match self {
            AgentModel::Gpt5 => "gpt-5",
            AgentModel::Gpt5Codex => "gpt-5-codex",
        }
    }

    pub fn from_str(value: &str) -> Self {
        match value {
            "gpt-5" => AgentModel::Gpt5,
            _ => AgentModel::Gpt5Codex,
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize, PartialEq, Eq)]
pub enum ReasoningBudget {
    High,
    Medium,
    Low,
}

impl ReasoningBudget {
    pub fn as_str(self) -> &'static str {
        match self {
            ReasoningBudget::High => "high",
            ReasoningBudget::Medium => "medium",
            ReasoningBudget::Low => "low",
        }
    }

    pub fn from_str(value: &str) -> Self {
        match value {
            "medium" => ReasoningBudget::Medium,
            "low" => ReasoningBudget::Low,
            _ => ReasoningBudget::High,
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize, PartialEq, Eq)]
pub enum TurnStatus {
    Launching,
    Running,
    Interactive,
    Stopped,
    Failed,
}

impl TurnStatus {
    pub fn as_str(self) -> &'static str {
        match self {
            TurnStatus::Launching => "launching",
            TurnStatus::Running => "running",
            TurnStatus::Interactive => "interactive",
            TurnStatus::Stopped => "stopped",
            TurnStatus::Failed => "failed",
        }
    }

    pub fn from_str(value: &str) -> Self {
        match value {
            "running" => TurnStatus::Running,
            "interactive" => TurnStatus::Interactive,
            "stopped" => TurnStatus::Stopped,
            "failed" => TurnStatus::Failed,
            _ => TurnStatus::Launching,
        }
    }
}
