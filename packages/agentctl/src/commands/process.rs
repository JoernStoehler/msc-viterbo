use std::time::{Duration, Instant};

use crate::error::CliError;

pub fn terminate_pid(pid: i64, wait: bool) -> Result<(), CliError> {
    use nix::sys::signal::{Signal, kill};
    use nix::unistd::Pid;

    let target = Pid::from_raw(pid as i32);
    match kill(target, Signal::SIGTERM) {
        Ok(_) => {}
        Err(nix::errno::Errno::ESRCH) => return Ok(()),
        Err(err) => {
            return Err(CliError::new(
                70,
                format!("Failed to signal process: {err}"),
            ));
        }
    }
    if wait {
        wait_for_pid(pid, Some(10))?;
    }
    Ok(())
}

pub fn wait_for_pid(pid: i64, timeout_secs: Option<u64>) -> Result<(), CliError> {
    let timeout = timeout_secs.unwrap_or(0);
    let start = Instant::now();
    loop {
        if !process_alive(pid) {
            return Ok(());
        }
        if timeout > 0 && start.elapsed() > Duration::from_secs(timeout) {
            return Err(CliError::new(
                124,
                format!("Process {pid} did not exit within {timeout}s"),
            ));
        }
        std::thread::sleep(Duration::from_millis(250));
    }
}

fn process_alive(pid: i64) -> bool {
    let rc = unsafe { nix::libc::kill(pid as nix::libc::pid_t, 0) };
    if rc == 0 {
        true
    } else {
        nix::errno::Errno::last_raw() != nix::libc::ESRCH
    }
}
