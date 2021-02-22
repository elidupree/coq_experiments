use crate::global_state_types::SharedState;
use parking_lot::Mutex;
use std::fs;
use std::sync::Arc;
use std::time::Duration;

impl SharedState {
    pub fn frequent_update(&mut self) {
        // If the code file has been modified, update it.
        if fs::metadata(&self.code_path)
            .and_then(|m| m.modified())
            .ok()
            != self.last_code_modified
        {
            if let Ok(mut code) = fs::read_to_string(&self.code_path) {
                if let Some(index) = code.find("STOP") {
                    code.truncate(index);
                }
                self.current_file_code = code;
                self.sertop_up_to_date_with_file = false;
            }
        }
    }
}

pub fn run(shared: Arc<Mutex<SharedState>>) {
    loop {
        let mut guard = shared.lock();
        guard.frequent_update();
        std::mem::drop(guard);
        std::thread::sleep(Duration::from_millis(10));
    }
}
