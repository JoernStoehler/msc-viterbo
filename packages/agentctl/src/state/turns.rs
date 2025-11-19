use std::path::Path;

use rusqlite::{OptionalExtension, params};

use crate::error::CliError;

use super::{Database, TurnRecord, TurnStatus, timestamp};

impl Database {
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

    pub fn mark_turn_interactive(
        &mut self,
        turn_id: i64,
        session_uuid: Option<&str>,
        pid: i64,
    ) -> Result<(), CliError> {
        let ts = timestamp();
        self.conn
            .execute(
                "
                UPDATE turns
                SET status = 'interactive', session_uuid = ?2, child_pid = ?3, last_active_at = ?4
                WHERE id = ?1
            ",
                params![turn_id, session_uuid, pid, ts],
            )
            .map_err(|err| CliError::new(70, format!("Failed to mark interactive: {err}")))?;
        Ok(())
    }

    pub fn update_session_uuid(
        &mut self,
        turn_id: i64,
        session_uuid: &str,
    ) -> Result<(), CliError> {
        let ts = timestamp();
        self.conn
            .execute(
                "
                UPDATE turns
                SET session_uuid = ?2, last_active_at = ?3
                WHERE id = ?1
            ",
                params![turn_id, session_uuid, ts],
            )
            .map_err(|err| CliError::new(70, format!("Failed to update session uuid: {err}")))?;
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
                WHERE handle = ?1 AND status IN ('launching', 'running', 'interactive')
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
        prompt_path: Path::new(&row.get::<_, String>(3)?).into(),
        log_path: Path::new(&row.get::<_, String>(4)?).into(),
        final_path: Path::new(&row.get::<_, String>(5)?).into(),
        turn_dir: Path::new(&row.get::<_, String>(6)?).into(),
        session_uuid: row.get(7)?,
        child_pid: row.get(8)?,
        started_at: row.get(9)?,
        last_active_at: row.get(10)?,
        stopped_at: row.get(11)?,
        failure_reason: row.get(12)?,
    })
}
