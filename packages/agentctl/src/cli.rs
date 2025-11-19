use clap::{Parser, Subcommand};

use crate::commands::{
    await_cmd::AwaitArgs, bootstrap::BootstrapArgs, define::DefineArgs, exec::ExecArgs,
    interactive::InteractiveArgs, list::ListArgs, print::PrintArgs, self_cmd::SelfArgs,
    start::StartArgs, stop::StopArgs,
};

#[derive(Parser)]
#[command(
    name = "agentctl",
    author,
    version,
    about = "Orchestrator for thesis agents"
)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Subcommand)]
pub enum Commands {
    List(ListArgs),
    Bootstrap(BootstrapArgs),
    Define(DefineArgs),
    Start(StartArgs),
    Stop(StopArgs),
    Await(AwaitArgs),
    Print(PrintArgs),
    Interactive(InteractiveArgs),
    #[command(name = "self")]
    SelfCmd(SelfArgs),
    #[command(name = "_exec", hide = true)]
    Exec(ExecArgs),
}
