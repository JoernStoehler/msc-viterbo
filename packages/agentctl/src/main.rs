mod cli;
mod commands;
mod error;
mod state;
mod util;

use std::process::ExitCode;

use clap::Parser;

use cli::{Cli, Commands};
use commands::{
    await_cmd, bootstrap, define, exec, interactive, list, print, self_cmd, start, stop,
};
use error::CliError;
use state::Database;
use util::ensure_repo_root;

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("Error: {}", err);
            ExitCode::from(err.exit_code())
        }
    }
}

fn run() -> Result<(), CliError> {
    let cli = Cli::parse();
    match cli.command {
        Commands::Exec(args) => exec::run(args),
        command => {
            let repo_root = ensure_repo_root()?;
            let mut db = Database::open(&repo_root)?;
            match command {
                Commands::List(args) => list::run(&mut db, args),
                Commands::Bootstrap(args) => bootstrap::run(&mut db, &repo_root, args),
                Commands::Define(args) => define::run(&mut db, args),
                Commands::Start(args) => start::run(&mut db, &repo_root, args),
                Commands::Stop(args) => stop::run(&mut db, args),
                Commands::Await(args) => await_cmd::run(&mut db, args),
                Commands::Print(args) => print::run(&mut db, args),
                Commands::Interactive(args) => interactive::run(&mut db, &repo_root, args),
                Commands::SelfCmd(args) => self_cmd::run(&mut db, args),
                Commands::Exec(_) => unreachable!(),
            }
        }
    }
}
