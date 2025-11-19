use std::fs;
use std::path::{Path, PathBuf};

use chrono::Utc;
use rusqlite::{Connection, OptionalExtension, params};
use serde::Serialize;

use crate::error::CliError;

const DB_FILE: &str = "state.db";

pub struct Database {
    conn: Connection,
}

impl Database {
    pub fn open(repo_root: &Path) -> Result<Self, CliError> {
        let agent_dir = repo_root.join(".agentctl");
        fs::create_dir_all(&agent_dir).map_err(|err| {
            CliError::new(
                70,
                format!("Failed to create {}: {err}", agent_dir.display()),
            )
        })?;
        let db_path = agent_dir.join(DB_FILE);
        let conn = Connection::open(db_path)
            .map_err(|err| CliError::new(70, format!("Failed to open agent DB: {err}")))?;
        conn.execute_batch("PRAGMA journal_mode = WAL; PRAGMA foreign_keys = ON;")
            .map_err(|err| CliError::new(70, format!("Failed to configure DB: {err}")))?;
        let db = Self { conn };
        db.migrate()?;
        Ok(db)
    }

    fn migrate(&self) -> Result<(), CliError> {
        self.conn
            .execute_batch(
                "
            CREATE TABLE IF NOT EXISTS worktrees (
                path TEXT PRIMARY KEY,
                branch TEXT NOT NULL,
                repo_root TEXT NOT NULL,
                bootstrapped_at TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS agents (
                handle TEXT PRIMARY KEY,
                worktree_path TEXT NOT NULL REFERENCES worktrees(path) ON DELETE CASCADE,
                parent_handle TEXT NOT NULL,
                model TEXT NOT NULL,
                reasoning_budget TEXT NOT NULL,
                defined_at TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS turns (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                handle TEXT NOT NULL REFERENCES agents(handle) ON DELETE CASCADE,
                status TEXT NOT NULL,
                prompt_path TEXT NOT NULL,
                log_path TEXT NOT NULL,
                final_path TEXT NOT NULL,
                turn_dir TEXT NOT NULL,
                session_uuid TEXT,
                child_pid INTEGER,
                started_at TEXT NOT NULL,
                last_active_at TEXT NOT NULL,
                stopped_at TEXT,
                failure_reason TEXT
            );
        ",
            )
            .map_err(|err| CliError::new(70, format!("Failed to run migrations: {err}")))
    }

    pub fn upsert_worktree(
        &mut self,
        path: &Path,
        branch: &str,
        repo_root: &Path,
    ) -> Result<(), CliError> {
        let ts = timestamp();
        self.conn
            .execute(
                "
                INSERT INTO worktrees(path, branch, repo_root, bootstrapped_at)
                VALUES (?1, ?2, ?3, ?4)
                ON CONFLICT(path) DO UPDATE SET branch = excluded.branch, repo_root = excluded.repo_root
            ",
                params![
                    path.display().to_string(),
                    branch,
                    repo_root.display().to_string(),
                    ts
                ],
            )
            .map_err(|err| CliError::new(70, format!("Failed to upsert worktree: {err}")))?;
        Ok(())
    }

    pub fn get_worktree(&self, path: &Path) -> Result<Option<WorktreeRecord>, CliError> {
        self.conn
            .query_row(
                "
                SELECT path, branch, repo_root, bootstrapped_at
                FROM worktrees WHERE path = ?1
            ",
                params![path.display().to_string()],
                |row| {
                    Ok(WorktreeRecord {
                        path: PathBuf::from(row.get::<_, String>(0)?),
                        branch: row.get(1)?,
                        repo_root: PathBuf::from(row.get::<_, String>(2)?),
                        bootstrapped_at: row.get(3)?,
                    })
                },
            )
            .optional()
            .map_err(|err| CliError::new(70, format!("Failed to fetch worktree: {err}")))
    }

    pub fn insert_agent(&mut self, agent: AgentRecord) -> Result<(), CliError> {
        self.conn
            .execute(
                "
                INSERT INTO agents(handle, worktree_path, parent_handle, model, reasoning_budget, defined_at)
                VALUES (?1, ?2, ?3, ?4, ?5, ?6)
            ",
                params![
                    agent.handle,
                    agent.worktree_path.display().to_string(),
                    agent.parent_handle,
                    agent.model.as_str(),
                    agent.reasoning_budget.as_str(),
                    agent.defined_at
                ],
            )
            .map_err(|err| CliError::new(70, format!("Failed to insert agent: {err}")))?;
        Ok(())
    }

    pub fn get_agent(&self, handle: &str) -> Result<Option<AgentRecord>, CliError> {
        self.conn
            .query_row(
                "
                SELECT handle, worktree_path, parent_handle, model, reasoning_budget, defined_at
                FROM agents WHERE handle = ?1
            ",
                params![handle],
                |row| {
                    Ok(AgentRecord {
                        handle: row.get(0)?,
                        worktree_path: PathBuf::from(row.get::<_, String>(1)?),
                        parent_handle: row.get(2)?,
                        model: AgentModel::from_str(&row.get::<_, String>(3)?),
                        reasoning_budget: ReasoningBudget::from_str(&row.get::<_, String>(4)?),
                        defined_at: row.get(5)?,
                    })
                },
            )
            .optional()
            .map_err(|err| CliError::new(70, format!("Failed to fetch agent: {err}")))
    }

    pub fn agents_for_worktree(&self, worktree: &Path) -> Result<Vec<AgentRecord>, CliError> {
        let mut stmt = self
            .conn
            .prepare(
                "
                SELECT handle, worktree_path, parent_handle, model, reasoning_budget, defined_at
                FROM agents WHERE worktree_path = ?1
            ",
            )
            .map_err(|err| CliError::new(70, format!("Failed to prepare agent query: {err}")))?;
        let rows = stmt
            .query_map(params![worktree.display().to_string()], |row| {
                Ok(AgentRecord {
                    handle: row.get(0)?,
                    worktree_path: PathBuf::from(row.get::<_, String>(1)?),
                    parent_handle: row.get(2)?,
                    model: AgentModel::from_str(&row.get::<_, String>(3)?),
                    reasoning_budget: ReasoningBudget::from_str(&row.get::<_, String>(4)?),
                    defined_at: row.get(5)?,
                })
            })
            .map_err(|err| CliError::new(70, format!("Failed to query agents: {err}")))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|err| CliError::new(70, format!("Failed to collect agents: {err}")))?;
        Ok(rows)
    }

    pub fn list_agents_with_status(&self) -> Result<Vec<AgentWithStatus>, CliError> {
        let mut stmt = self
            .conn
            .prepare(
                "
                WITH latest AS (
                    SELECT t.handle, t.status, t.last_active_at
                    FROM turns t
                    JOIN (
                        SELECT handle, MAX(id) AS id FROM turns GROUP BY handle
                    ) grouped ON grouped.handle = t.handle AND grouped.id = t.id
                )
                SELECT a.handle, a.worktree_path, a.parent_handle, a.model, a.reasoning_budget, a.defined_at,
                       latest.status, latest.last_active_at
                FROM agents a
                LEFT JOIN latest ON latest.handle = a.handle
                ORDER BY a.handle ASC
            ",
            )
            .map_err(|err| CliError::new(70, format!("Failed to prepare list query: {err}")))?;
        let rows = stmt
            .query_map([], |row| {
                Ok(AgentWithStatus {
                    agent: AgentRecord {
                        handle: row.get(0)?,
                        worktree_path: PathBuf::from(row.get::<_, String>(1)?),
                        parent_handle: row.get(2)?,
                        model: AgentModel::from_str(&row.get::<_, String>(3)?),
                        reasoning_budget: ReasoningBudget::from_str(&row.get::<_, String>(4)?),
                        defined_at: row.get(5)?,
                    },
                    status: row
                        .get::<_, Option<String>>(6)?
                        .map(|s| TurnStatus::from_str(&s)),
                    last_active: row.get(7)?,
                })
            })
            .map_err(|err| CliError::new(70, format!("Failed to map agents: {err}")))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|err| CliError::new(70, format!("Failed to collect rows: {err}")))?;
        Ok(rows)
    }

    pub fn create_turn(
        &mut self,
        handle: &str,
        prompt_path: &Path,
        log_path: &Path,
        final_path: &Path,
        turn_dir: &Path,
        started_at: &str,
    ) -> Result<i64, CliError> {
        let last_active = started_at.to_string();
        self.conn
            .execute(
                "
                INSERT INTO turns(handle, status, prompt_path, log_path, final_path, turn_dir, started_at, last_active_at)
                VALUES (?1, 'launching', ?2, ?3, ?4, ?5, ?6, ?7)
            ",
                params![
                    handle,
                    prompt_path.display().to_string(),
                    log_path.display().to_string(),
                    final_path.display().to_string(),
                    turn_dir.display().to_string(),
                    started_at,
                    last_active
                ],
            )
            .map_err(|err| CliError::new(70, format!("Failed to insert turn: {err}")))?;
        Ok(self.conn.last_insert_rowid())
    }

    pub fn mark_turn_running(
        &mut self,
        turn_id: i64,
        session_uuid: &str,
        pid: i64,
    ) -> Result<(), CliError> {
        let ts = timestamp();
        self.conn
            .execute(
                "
                UPDATE turns
                SET status = 'running', session_uuid = ?2, child_pid = ?3, last_active_at = ?4
                WHERE id = ?1
            ",
                params![turn_id, session_uuid, pid, ts],
            )
            .map_err(|err| CliError::new(70, format!("Failed to mark running: {err}")))?;
        Ok(())
    }

    pub fn mark_turn_failed(&mut self, turn_id: i64, reason: &str) -> Result<(), CliError> {
        let ts = timestamp();
        self.conn
            .execute(
                "
                UPDATE turns
                SET status = 'failed', stopped_at = ?2, last_active_at = ?2, failure_reason = ?3
                WHERE id = ?1
            ",
                params![turn_id, ts, reason],
            )
            .map_err(|err| CliError::new(70, format!("Failed to mark failed: {err}")))?;
        Ok(())
    }

    pub fn mark_turn_stopped(
        &mut self,
        turn_id: i64,
        status: TurnStatus,
        reason: Option<&str>,
    ) -> Result<(), CliError> {
        let ts = timestamp();
        let status_str = status.as_str();
        self.conn
            .execute(
                "
                UPDATE turns
                SET status = ?2, stopped_at = ?3, last_active_at = ?3, failure_reason = ?4
                WHERE id = ?1
            ",
                params![turn_id, status_str, ts, reason],
            )
            .map_err(|err| CliError::new(70, format!("Failed to mark stopped: {err}")))?;
        Ok(())
    }

    pub fn get_active_turn(&self, handle: &str) -> Result<Option<TurnRecord>, CliError> {
        self.conn
            .query_row(
                "
                SELECT id, handle, status, prompt_path, log_path, final_path, turn_dir, session_uuid,
                       child_pid, started_at, last_active_at, stopped_at, failure_reason
                FROM turns
                WHERE handle = ?1 AND status IN ('launching', 'running')
                ORDER BY id DESC
                LIMIT 1
            ",
                params![handle],
                row_to_turn,
            )
            .optional()
            .map_err(|err| CliError::new(70, format!("Failed to fetch active turn: {err}")))
    }

    pub fn list_recent_turns(&self, handle: &str, limit: i64) -> Result<Vec<TurnRecord>, CliError> {
        let mut stmt = self
            .conn
            .prepare(
                "
                SELECT id, handle, status, prompt_path, log_path, final_path, turn_dir, session_uuid,
                       child_pid, started_at, last_active_at, stopped_at, failure_reason
                FROM turns
                WHERE handle = ?1
                ORDER BY id DESC
                LIMIT ?2
            ",
            )
            .map_err(|err| CliError::new(70, format!("Failed to prepare turn list: {err}")))?;
        let rows = stmt
            .query_map(params![handle, limit], row_to_turn)
            .map_err(|err| CliError::new(70, format!("Failed to query turns: {err}")))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|err| CliError::new(70, format!("Failed to collect turns: {err}")))?;
        Ok(rows)
    }

    pub fn last_session_uuid(&self, handle: &str) -> Result<Option<String>, CliError> {
        self.conn
            .query_row(
                "
                SELECT session_uuid
                FROM turns
                WHERE handle = ?1 AND session_uuid IS NOT NULL
                ORDER BY id DESC
                LIMIT 1
            ",
                params![handle],
                |row| row.get(0),
            )
            .optional()
            .map_err(|err| CliError::new(70, format!("Failed to fetch session uuid: {err}")))
    }
}

fn row_to_turn(row: &rusqlite::Row<'_>) -> rusqlite::Result<TurnRecord> {
    Ok(TurnRecord {
        id: row.get(0)?,
        handle: row.get(1)?,
        status: TurnStatus::from_str(&row.get::<_, String>(2)?),
        prompt_path: PathBuf::from(row.get::<_, String>(3)?),
        log_path: PathBuf::from(row.get::<_, String>(4)?),
        final_path: PathBuf::from(row.get::<_, String>(5)?),
        turn_dir: PathBuf::from(row.get::<_, String>(6)?),
        session_uuid: row.get(7)?,
        child_pid: row.get(8)?,
        started_at: row.get(9)?,
        last_active_at: row.get(10)?,
        stopped_at: row.get(11)?,
        failure_reason: row.get(12)?,
    })
}

pub fn timestamp() -> String {
    Utc::now().to_rfc3339_opts(chrono::SecondsFormat::Secs, true)
}

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
    Stopped,
    Failed,
}

impl TurnStatus {
    pub fn as_str(self) -> &'static str {
        match self {
            TurnStatus::Launching => "launching",
            TurnStatus::Running => "running",
            TurnStatus::Stopped => "stopped",
            TurnStatus::Failed => "failed",
        }
    }

    pub fn from_str(value: &str) -> Self {
        match value {
            "running" => TurnStatus::Running,
            "stopped" => TurnStatus::Stopped,
            "failed" => TurnStatus::Failed,
            _ => TurnStatus::Launching,
        }
    }
}
