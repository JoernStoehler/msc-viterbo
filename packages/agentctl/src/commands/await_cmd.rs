use clap::Args;

use crate::{error::CliError, state::Database};

use super::process::wait_for_pid;

#[derive(Args, Clone)]
pub struct AwaitArgs {
    pub handle: String,
    #[arg(long)]
    pub timeout: Option<u64>,
}

pub fn run(db: &mut Database, args: AwaitArgs) -> Result<(), CliError> {
    let turn = db
        .get_active_turn(&args.handle)?
        .ok_or_else(|| CliError::new(65, format!("No running turn for {}", args.handle)))?;
    if let Some(pid) = turn.child_pid {
        wait_for_pid(pid, args.timeout)?;
    }
    println!("Agent {} completed.", args.handle);
    Ok(())
}
