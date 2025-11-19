use clap::Args;

use crate::{
    error::CliError,
    state::{Database, TurnStatus},
};

use super::process::terminate_pid;

#[derive(Args, Clone)]
pub struct StopArgs {
    pub handle: String,
}

pub fn run(db: &mut Database, args: StopArgs) -> Result<(), CliError> {
    let turn = db
        .get_active_turn(&args.handle)?
        .ok_or_else(|| CliError::new(65, format!("No running turn for {}", args.handle)))?;
    let pid = turn
        .child_pid
        .ok_or_else(|| CliError::new(65, "Turn has no recorded exec pid".to_string()))?;
    terminate_pid(pid, true)?;
    db.mark_turn_stopped(turn.id, TurnStatus::Stopped, Some("stopped via agentctl"))?;
    println!("Stopped agent {}.", args.handle);
    Ok(())
}
