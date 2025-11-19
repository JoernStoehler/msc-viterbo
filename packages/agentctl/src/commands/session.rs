use std::fs;
use std::path::{Path, PathBuf};

use crate::{
    error::CliError,
    state::{self, AgentRecord},
    util,
};

pub fn prepare_turn_dir(agent: &AgentRecord, repo_root: &Path) -> Result<PathBuf, CliError> {
    let base = util::sessions_root(repo_root)?
        .join("sessions")
        .join(&agent.handle);
    fs::create_dir_all(&base)
        .map_err(|err| CliError::new(70, format!("Failed to create {}: {err}", base.display())))?;
    let timestamp = state::timestamp().replace(':', "-");
    let dir = base.join(format!("turn-{timestamp}"));
    fs::create_dir_all(&dir)
        .map_err(|err| CliError::new(70, format!("Failed to create {}: {err}", dir.display())))?;
    Ok(dir)
}
