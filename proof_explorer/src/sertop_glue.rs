use crate::global_state_types::MessageToMainThread;
use crate::serapi_protocol::Answer;
use std::io::{BufRead, BufReader};
use std::process::ChildStdout;
use std::sync::mpsc::Sender;

pub struct Interrupted;
#[allow(clippy::large_enum_variant)] // it's expected that it will *usually* be the large variant
#[derive(Debug)]
pub enum MessageFromSertop {
    InterruptedWhileNoCommandRunning,
    Invalid,
    Answer(Answer),
}

fn interpret_sertop_line(line: String) -> MessageFromSertop {
    // note that there are to different ways sertop response to interrupts:
    // Sys.Break if there is no command running;
    // (Answer N(CoqExn ... str"\nUser interrupt")))) if there is a command running.
    if line.trim() == "Sys.Break" {
        eprintln!("received Sys.Break from sertop\n");
        return MessageFromSertop::InterruptedWhileNoCommandRunning;
    }
    let parsed = serde_lexpr::parse::from_str(&line);
    let parsed = match parsed {
        Ok(parsed) => parsed,
        Err(err) => {
            eprintln!(
                "received invalid S-expression from sertop ({:?}):\n{}\n",
                err, line
            );
            return MessageFromSertop::Invalid;
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
            return MessageFromSertop::Invalid;
        }
    };
    eprintln!(
        "received valid input from sertop: {:?}\n{}\n",
        interpreted, line
    );
    MessageFromSertop::Answer(interpreted)
}

pub fn listen(child_stdout: ChildStdout, sender: Sender<MessageToMainThread>) {
    for line in BufReader::new(child_stdout).lines() {
        let line = line.expect("IO error receiving from sertop?");
        sender
            .send(MessageToMainThread::FromSertop(interpret_sertop_line(line)))
            .expect("main thread should never drop receiver");
    }
}
