use std::path::Path;

use clap::Args;

use crate::{error::CliError, state::Database};

#[derive(Args, Clone)]
pub struct PrintArgs {
    pub handle: String,
    #[arg(long = "last", default_value_t = 1)]
    pub last: u32,
    #[arg(long)]
    pub json: bool,
}

pub fn run(db: &mut Database, args: PrintArgs) -> Result<(), CliError> {
    let turns = db.list_recent_turns(&args.handle, args.last as i64)?;
    if args.json {
        println!(
            "{}",
            serde_json::to_string_pretty(&turns)
                .map_err(|err| CliError::new(1, err.to_string()))?
        );
        return Ok(());
    }
    for turn in turns {
        println!("Turn {} ({})", turn.id, turn.status.as_str());
        println!("started: {}", turn.started_at);
        if let Some(stopped) = &turn.stopped_at {
            println!("stopped: {}", stopped);
        }
        if let Some(uuid) = &turn.session_uuid {
            println!("session_uuid: {}", uuid);
        }
        println!("prompt:");
        print_file(&turn.prompt_path)?;
        println!("final message:");
        if turn.final_path.exists() {
            print_file(&turn.final_path)?;
        } else {
            println!("[no final message yet]");
        }
        println!();
    }
    Ok(())
}

fn print_file(path: &Path) -> Result<(), CliError> {
    match std::fs::read_to_string(path) {
        Ok(content) => println!("{content}"),
        Err(err) => println!("(unable to read {}: {err})", path.display()),
    }
    Ok(())
}
