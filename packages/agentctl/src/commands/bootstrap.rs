use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

use clap::Args;

use crate::{
    error::CliError,
    state::Database,
    util::{canonicalize, git_current_branch},
};

#[derive(Args, Clone)]
pub struct BootstrapArgs {
    pub worktree: PathBuf,
}

pub fn run(db: &mut Database, repo_root: &Path, args: BootstrapArgs) -> Result<(), CliError> {
    let path = canonicalize(&args.worktree)?;
    if !path.exists() {
        return Err(CliError::new(
            65,
            format!("Worktree {} does not exist", path.display()),
        ));
    }
    if !path.starts_with(repo_root) {
        return Err(CliError::new(
            65,
            format!(
                "Worktree {} is outside repo {}",
                path.display(),
                repo_root.display()
            ),
        ));
    }
    let branch = git_current_branch(&path)?;
    db.upsert_worktree(&path, &branch, repo_root)?;
    run_bootstrap_hook(repo_root, &path, &branch)?;
    println!(
        "Bootstrapped worktree {} (branch {})",
        path.display(),
        branch
    );
    Ok(())
}

fn run_bootstrap_hook(repo_root: &Path, worktree: &Path, branch: &str) -> Result<(), CliError> {
    let hook = match env::var("AGENTCTL_BOOTSTRAP_HOOK") {
        Ok(value) if !value.trim().is_empty() => value,
        _ => return Ok(()),
    };
    let status = Command::new("bash")
        .arg("-lc")
        .arg(hook)
        .current_dir(repo_root)
        .env("AGENTCTL_REPO_ROOT", repo_root.display().to_string())
        .env("AGENTCTL_WORKTREE", worktree.display().to_string())
        .env("AGENTCTL_WORKTREE_BRANCH", branch)
        .status()
        .map_err(|err| CliError::new(70, format!("Bootstrap hook failed to start: {err}")))?;
    if !status.success() {
        return Err(CliError::new(
            70,
            format!("Bootstrap hook exited with {}", status),
        ));
    }
    Ok(())
}
