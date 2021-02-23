use crate::global_state_types::{MessageFromOutsideSertop, MessageToMainThread, SharedState};
use parking_lot::Mutex;
use std::fs;
use std::path::PathBuf;
use std::sync::mpsc::Sender;
use std::sync::Arc;
use std::time::Duration;

pub enum MessageFromSupervisor {
    ReplaceFile(String),
}

pub fn run(code_path: PathBuf, sender: Sender<MessageToMainThread>) {
    // TODO : this isn't the most efficient file watcher system, figure out what is?
    let mut last_code_modified = None;
    let mut last_observed_code = String::new();
    loop {
        // If the code file has been modified, update it.
        let modified = fs::metadata(&code_path).and_then(|m| m.modified()).ok();
        if modified != last_code_modified {
            last_code_modified = modified;
            if let Ok(mut code) = fs::read_to_string(&code_path) {
                if let Some(index) = code.find("STOP") {
                    code.truncate(index);
                }
                if code != last_observed_code {
                    last_observed_code = code.clone();
                    sender.send(MessageToMainThread::FromOutsideSertop(
                        MessageFromOutsideSertop::FromSupervisor(
                            MessageFromSupervisor::ReplaceFile(code),
                        ),
                    ));
                }
            }
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}
