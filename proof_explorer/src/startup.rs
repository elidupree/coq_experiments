use crate::global_state_types::{CommandRunner, MainThreadState, RocketState, SharedState};
use crate::{sertop_glue, supervisor_thread, webserver_glue};
use parking_lot::Mutex;
use std::default::default;
use std::path::PathBuf;
use std::process;
use std::process::Stdio;
use std::sync::mpsc::channel;
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

    let shared = Arc::new(Mutex::new(SharedState::new(code_path.clone())));
    let (sender, receiver) = channel();

    std::thread::spawn({
        let sender = sender.clone();
        move || supervisor_thread::run(code_path, sender)
    });
    std::thread::spawn({
        let sender = sender.clone();
        move || sertop_glue::listen(child_stdout, sender)
    });

    std::thread::spawn({
        let mut main_thread = MainThreadState {
            command_runner: CommandRunner {
                receiver,
                child_stdin,
                shared: shared.clone(),
                messages_from_outside_sertop_queue: default(),
            },
            sertop_state: default(),
            shared: shared.clone(),
            last_added_file_code: String::new(),
            end_of_first_added_from_file_that_failed_to_execute: None,
        };
        move || {
            main_thread.run();
        }
    });

    webserver_glue::launch(RocketState {
        shared,
        sender: Mutex::new(sender),
    });
}
