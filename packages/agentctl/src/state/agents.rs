use std::path::PathBuf;

use rusqlite::{OptionalExtension, params};

use crate::error::CliError;

use super::{AgentModel, AgentRecord, AgentWithStatus, Database, ReasoningBudget, TurnStatus};

impl Database {
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
}
