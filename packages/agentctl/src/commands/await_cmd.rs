use clap::Args;

use std::time::{Duration, Instant};

use crate::{
    error::CliError,
    state::{Database, TurnStatus},
};

use super::process::wait_for_pid;

#[derive(Args, Clone)]
pub struct AwaitArgs {
    pub handle: String,
    #[arg(long)]
    pub timeout: Option<u64>,
}

pub fn run(db: &mut Database, args: AwaitArgs) -> Result<(), CliError> {
    let deadline = args
        .timeout
        .map(|secs| Instant::now() + Duration::from_secs(secs));
    loop {
        check_deadline(deadline)?;
        let turn = match db.get_active_turn(&args.handle)? {
            Some(turn) => turn,
            None => {
                println!("Agent {} completed.", args.handle);
                return Ok(());
            }
        };
        let pid = match turn.child_pid {
            Some(pid) => pid,
            None => {
                std::thread::sleep(Duration::from_millis(100));
                continue;
            }
        };
        let remaining_secs = deadline.map(|dl| {
            let now = Instant::now();
            if dl <= now {
                1
            } else {
                let secs = dl.saturating_duration_since(now).as_secs();
                if secs == 0 { 1 } else { secs }
            }
        });
        wait_for_pid(pid, remaining_secs)?;
        if wait_for_completion(db, &args.handle)? {
            println!("Agent {} completed.", args.handle);
            return Ok(());
        }
        // `_exec` exited but turn still marked running; mark it manually.
        db.mark_turn_stopped(
            turn.id,
            TurnStatus::Stopped,
            Some("stopped via agentctl await"),
        )?;
        println!("Agent {} completed.", args.handle);
        return Ok(());
    }
}

fn check_deadline(deadline: Option<Instant>) -> Result<(), CliError> {
    if let Some(deadline) = deadline
        && Instant::now() >= deadline
    {
        return Err(CliError::new(
            124,
            "Turn is still running after the specified timeout.",
        ));
    }
    Ok(())
}

fn wait_for_completion(db: &mut Database, handle: &str) -> Result<bool, CliError> {
    let settle_deadline = Instant::now() + Duration::from_secs(5);
    loop {
        if db.get_active_turn(handle)?.is_none() {
            return Ok(true);
        }
        if Instant::now() >= settle_deadline {
            return Ok(false);
        }
        std::thread::sleep(Duration::from_millis(100));
    }
}
