use crate::global_state_types::{CommandRunner, SertopThreadState, SharedState};
use crate::{supervisor_thread, webserver_glue};
use parking_lot::Mutex;
use std::default::default;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;
use std::process;
use std::process::Stdio;
use std::sync::Arc;

pub fn run(code_path: PathBuf) {
    // Hack: Compile the scss at the beginning of the main program.
    // This would be better as some sort of build script, but that's not a big concern right now
    // TODO: improve on that
    let scss_path = "./style.scss";
    let css_path = "./static/media/style.css";
    let sass_status = process::Command::new("sass")
        .args(&[scss_path, css_path])
        .status()
        .expect("error getting sass status");
    assert!(sass_status.success(), "sass failed");

    let child = process::Command::new("sertop")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed sertop command");
    let child_stdout = child.stdout.expect("no stdout?");
    let child_stdin = child.stdin.expect("no stdin?");

    let shared = Arc::new(Mutex::new(SharedState::new(code_path)));

    std::thread::spawn({
        let mut sertop_thread = SertopThreadState {
            command_runner: CommandRunner {
                lines_iterator: BufReader::new(child_stdout).lines(),
                child_stdin,
                shared: shared.clone(),
            },
            sertop_state: default(),
            shared: shared.clone(),
            last_added_file_code: String::new(),
            end_of_first_added_from_file_that_failed_to_execute: None,
        };
        move || {
            sertop_thread.run();
        }
    });

    std::thread::spawn({
        let shared = shared.clone();
        move || {
            supervisor_thread::run(shared);
        }
    });

    webserver_glue::launch(shared);
}
