use std::path::{Path, PathBuf};

use rusqlite::{OptionalExtension, params};

use crate::error::CliError;

use super::{Database, WorktreeRecord, timestamp};

impl Database {
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
}
