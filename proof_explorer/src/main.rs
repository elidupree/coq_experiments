//use anyhow::{anyhow, Context};
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};
use serde_lexpr::Value;
use std::io::{BufRead, BufReader};
use std::process::{ChildStdin, ChildStdout, Command, Stdio};
use std::thread;
use std::time::Duration;

fn main() {
    let child = Command::new("sertop")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed sertop command");
    let child_stdout = child.stdout.expect("no stdout?");
    receiver_thread(child_stdout);
}

#[derive(Clone, Debug, Serialize, Deserialize)]
enum FeedbackContent {
    Processed,
    Incomplete,
    Complete,
    ProcessingIn(String),
    InProgress(i64),
    WorkerStatus(String, String),
    AddedAcxiom,
    FileDependency(Option<String>, String),
    FileLoaded(String, String),
    Message {
        level: i64,
        loc: Option<()>,
        pp: (),
        str: String,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct Feedback {
    doc_id: i64,
    span_id: i64,
    route: i64,
    contents: FeedbackContent,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
enum Answer {
    Feedback(Feedback),
    Other,
}

pub fn receiver_thread(child_stdout: ChildStdout) {
    for line in BufReader::new(child_stdout).lines() {
        let line = line.unwrap();
        let parsed = serde_lexpr::parse::from_str(&line);
        let parsed: serde_lexpr::Value = match parsed {
            Ok(parsed) => parsed,
            Err(err) => {
                eprintln!(
                    "received invalid S-expression from sertop ({:?}):\n{}\n",
                    err, line
                );
                continue;
            }
        };
        let interpreted: Result<Answer, _> = serde_lexpr::from_value(&parsed); //serde_lexpr::from_str(&line.replace("(", " ("));

        let interpreted = match interpreted {
            Ok(interpreted) => interpreted,
            Err(err) => {
                eprintln!(
                    "received invalid Answer from sertop ({:?}):\n{}\n{}\n",
                    err, parsed, line,
                );
                continue;
            }
        };
        eprintln!("received valid input from sertop: {:#?}\n", interpreted);
    }
}
