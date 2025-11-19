use crate::{
    error::CliError,
    state::{AgentWithStatus, Database},
    util::format_table,
};
use clap::Args;

#[derive(Args, Clone, Copy)]
pub struct ListArgs {
    #[arg(long)]
    pub json: bool,
}

pub fn run(db: &mut Database, args: ListArgs) -> Result<(), CliError> {
    let rows = db.list_agents_with_status()?;
    if args.json {
        let payload =
            serde_json::to_string_pretty(&rows).map_err(|err| CliError::new(1, err.to_string()))?;
        println!("{payload}");
        return Ok(());
    }

    let mut table = Vec::with_capacity(rows.len() + 1);
    table.push(vec![
        "handle".into(),
        "worktree".into(),
        "parent".into(),
        "model".into(),
        "budget".into(),
        "status".into(),
        "last_active".into(),
    ]);
    for AgentWithStatus {
        agent,
        status,
        last_active,
    } in rows
    {
        table.push(vec![
            agent.handle.clone(),
            agent.worktree_path.display().to_string(),
            agent.parent_handle.clone(),
            agent.model.as_str().to_string(),
            agent.reasoning_budget.as_str().to_string(),
            status
                .map(|s| s.as_str().to_string())
                .unwrap_or_else(|| "idle".into()),
            last_active.unwrap_or_else(|| agent.defined_at.clone()),
        ]);
    }
    println!("{}", format_table(&table));
    Ok(())
}
