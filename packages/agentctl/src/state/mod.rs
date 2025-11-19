use std::path::Path;

use chrono::Utc;
use rusqlite::Connection;

use crate::{error::CliError, util};

mod agents;
mod records;
mod turns;
mod worktrees;

pub use records::{
    AgentModel, AgentRecord, AgentWithStatus, ReasoningBudget, TurnRecord, TurnStatus,
    WorktreeRecord,
};

const DB_FILE: &str = "state.db";

pub struct Database {
    pub(crate) conn: Connection,
}

impl Database {
    pub fn open(repo_root: &Path) -> Result<Self, CliError> {
        let storage_root = util::sessions_root(repo_root)?;
        let db_path = storage_root.join(DB_FILE);
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
}

pub fn timestamp() -> String {
    Utc::now().to_rfc3339_opts(chrono::SecondsFormat::Secs, true)
}
