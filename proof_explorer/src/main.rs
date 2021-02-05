//use anyhow::{anyhow, Context};
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};
use std::io::{BufRead, BufReader, Write};
use std::process::{self, ChildStdin, ChildStdout, Stdio};
use std::thread;
use std::time::Duration;

mod serapi_protocol;

use crate::serapi_protocol::*;

fn main() {
    let child = process::Command::new("sertop")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed sertop command");
    let child_stdout = child.stdout.expect("no stdout?");
    let child_stdin = child.stdin.expect("no stdin?");
    thread::spawn(move || other_thread(child_stdin));
    receiver_thread(child_stdout);
}

pub fn receiver_thread(child_stdout: ChildStdout) {
    for line in BufReader::new(child_stdout).lines() {
        let line = line.unwrap();
        let parsed = serde_lexpr::parse::from_str(&line);
        let parsed = match parsed {
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
        eprintln!(
            "received valid input from sertop:\n{:?}\n{}\n",
            interpreted, line
        );

        match interpreted {
            Answer::Feedback(feedback) => match feedback.contents {
                FeedbackContent::Processed => {}
                _ => {}
            },
            Answer::Answer(command_tag, answer_kind) => match answer_kind {
                AnswerKind::Added(state_id, location, extra) => {}
                _ => {}
            },
        }
    }
}

pub fn send_command(child_stdin: &mut ChildStdin, command: &Command) {
    let text = serde_lexpr::to_string(command).unwrap();
    eprintln!("sending command to sertop: {}\n", text);
    writeln!(child_stdin, "{}", text);
}

pub fn other_thread(mut child_stdin: ChildStdin) {
    send_command(
        &mut child_stdin,
        &Command::Add(
            Default::default(),
            "Lemma foo : forall x : nat, x = x.".to_string(),
        ),
    );
    send_command(&mut child_stdin, &Command::Exec(2));
}
