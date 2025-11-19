use std::env;
use std::path::Path;

use clap::Args;

use crate::{error::CliError, state::Database, util::canonicalize};

#[derive(Args, Clone, Copy)]
pub struct SelfArgs {
    #[arg(long)]
    pub json: bool,
}

pub fn run(db: &mut Database, args: SelfArgs) -> Result<(), CliError> {
    let handle = match env::var("AGENTCTL_HANDLE") {
        Ok(handle) => handle,
        Err(_) => {
            let cwd = env::current_dir()
                .map_err(|err| CliError::new(65, format!("Unable to read current dir: {err}")))?;
            let path = canonicalize(&cwd)?;
            return print_unbound_self(&path, args.json);
        }
    };
    let record = db
        .get_agent(&handle)?
        .ok_or_else(|| CliError::new(65, format!("Unknown handle {}", handle)))?;
    if args.json {
        println!(
            "{}",
            serde_json::to_string_pretty(&record)
                .map_err(|err| CliError::new(1, err.to_string()))?
        );
    } else {
        println!("handle: {}", record.handle);
        println!("worktree: {}", record.worktree_path.display());
        println!("parent: {}", record.parent_handle);
        println!("model: {}", record.model.as_str());
        println!("budget: {}", record.reasoning_budget.as_str());
        println!("defined_at: {}", record.defined_at);
    }
    Ok(())
}

fn print_unbound_self(path: &Path, json: bool) -> Result<(), CliError> {
    if json {
        let payload = serde_json::json!({
            "handle": serde_json::Value::Null,
            "worktree_path": path.display().to_string(),
            "parent_handle": serde_json::Value::Null,
            "model": serde_json::Value::Null,
            "reasoning_budget": serde_json::Value::Null,
            "defined_at": serde_json::Value::Null
        });
        println!(
            "{}",
            serde_json::to_string_pretty(&payload)
                .map_err(|err| CliError::new(1, err.to_string()))?
        );
    } else {
        println!("handle: undefined");
        println!("worktree: {}", path.display());
        println!("parent: none");
        println!("model: none");
        println!("budget: none");
        println!("defined_at: none");
    }
    Ok(())
}
