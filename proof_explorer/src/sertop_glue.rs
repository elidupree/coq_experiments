use crate::serapi_protocol::Answer;

pub struct Interrupted;
#[allow(clippy::large_enum_variant)] // it's expected that it will *usually* be the large variant
pub enum AnswersStreamItem {
    InterruptedWhileNoCommandRunning,
    Invalid,
    Answer(Answer),
}

pub fn interpret_sertop_line(line: String) -> AnswersStreamItem {
    // note that there are to different ways sertop response to interrupts:
    // Sys.Break if there is no command running;
    // (Answer N(CoqExn ... str"\nUser interrupt")))) if there is a command running.
    if line.trim() == "Sys.Break" {
        return AnswersStreamItem::InterruptedWhileNoCommandRunning;
    }
    let parsed = serde_lexpr::parse::from_str(&line);
    let parsed = match parsed {
        Ok(parsed) => parsed,
        Err(err) => {
            eprintln!(
                "received invalid S-expression from sertop ({:?}):\n{}\n",
                err, line
            );
            return AnswersStreamItem::Invalid;
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
            return AnswersStreamItem::Invalid;
        }
    };
    eprintln!(
        "received valid input from sertop: {:?}\n{}\n",
        interpreted, line
    );
    AnswersStreamItem::Answer(interpreted)
}
