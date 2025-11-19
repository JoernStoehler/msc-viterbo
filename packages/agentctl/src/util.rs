use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::error::CliError;

pub fn ensure_repo_root() -> Result<PathBuf, CliError> {
    let output = Command::new("git")
        .arg("rev-parse")
        .arg("--show-toplevel")
        .output()
        .map_err(|err| CliError::new(70, format!("git rev-parse failed: {err}")))?;
    if !output.status.success() {
        return Err(CliError::new(
            70,
            String::from_utf8_lossy(&output.stderr).trim().to_string(),
        ));
    }
    Ok(PathBuf::from(
        String::from_utf8_lossy(&output.stdout).trim(),
    ))
}

pub fn canonicalize(path: &Path) -> Result<PathBuf, CliError> {
    std::fs::canonicalize(path).map_err(|err| {
        CliError::new(
            65,
            format!("Failed to canonicalize {}: {err}", path.display()),
        )
    })
}

pub fn git_current_branch(path: &Path) -> Result<String, CliError> {
    let output = Command::new("git")
        .arg("-C")
        .arg(path)
        .arg("rev-parse")
        .arg("--abbrev-ref")
        .arg("HEAD")
        .output()
        .map_err(|err| CliError::new(70, format!("git rev-parse failed: {err}")))?;
    if !output.status.success() {
        return Err(CliError::new(
            70,
            String::from_utf8_lossy(&output.stderr).trim().to_string(),
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

pub fn format_table(rows: &[Vec<String>]) -> String {
    if rows.is_empty() {
        return String::new();
    }
    let col_count = rows.iter().map(|r| r.len()).max().unwrap_or(0);
    let mut widths = vec![0usize; col_count];
    for row in rows {
        for (idx, cell) in row.iter().enumerate() {
            widths[idx] = widths[idx].max(cell.len());
        }
    }
    let mut out = Vec::with_capacity(rows.len());
    for row in rows {
        let mut line = Vec::with_capacity(row.len());
        for (idx, cell) in row.iter().enumerate() {
            line.push(format!("{cell:<width$}", width = widths[idx]));
        }
        out.push(line.join(" "));
    }
    out.join("\n")
}

pub fn validate_handle(handle: &str) -> Result<(), CliError> {
    if handle.is_empty() {
        return Err(CliError::new(65, "Handle cannot be empty"));
    }
    if handle
        .chars()
        .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || matches!(c, '-' | '_' | '.'))
    {
        Ok(())
    } else {
        Err(CliError::new(
            65,
            "Handle must contain only lowercase letters, digits, '-', '_' or '.'",
        ))
    }
}

pub fn repo_slug(repo_root: &Path) -> String {
    repo_root
        .components()
        .map(|c| c.as_os_str().to_string_lossy().replace('/', "_"))
        .collect::<Vec<_>>()
        .join("_")
}

pub fn sessions_root(repo_root: &Path) -> Result<PathBuf, CliError> {
    let home = env::var("HOME").map_err(|err| CliError::new(70, format!("HOME not set: {err}")))?;
    let base = PathBuf::from(home)
        .join(".agentctl")
        .join("repos")
        .join(repo_slug(repo_root));
    fs::create_dir_all(base.join("sessions")).map_err(|err| {
        CliError::new(
            70,
            format!(
                "Failed to prepare {}: {err}",
                base.join("sessions").display()
            ),
        )
    })?;
    Ok(base)
}
