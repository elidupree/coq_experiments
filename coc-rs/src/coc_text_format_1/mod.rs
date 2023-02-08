mod display;
mod from_constructors;
mod metavariable_conversions;

#[allow(clippy::all)]
mod lalrpop_wrapper {
    use lalrpop_util::lalrpop_mod;
    lalrpop_mod!(pub(crate) coc_text_format_1, "/coc_text_format_1/coc_text_format_1.rs");
}

pub use self::lalrpop_wrapper::coc_text_format_1::CommandParser;
use live_prop_test::{live_prop_test, lpt_assert_eq};
use regex::{Captures, Regex};
use std::borrow::Cow;

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Command {
    Assign(String, Formula),
    ClaimType(String, Formula),
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Default)]
pub enum AbstractionKind {
    Lambda,
    #[default]
    ForAll,
}

#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct Abstraction {
    kind: AbstractionKind,
    parameter_name: String,
    parameter_type: Formula,
    body: Formula,
}

#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub enum Formula {
    Prop,
    Usage(String),
    #[default]
    Hole,
    Abstraction(Box<Abstraction>),
    Apply(Box<[Formula; 2]>),
}

pub struct Document {
    commands: Vec<Command>,
}

fn command_regex() -> Regex {
    Regex::new(r"(?m)^>([^\.]*)\.").unwrap()
}

impl Document {
    pub fn parse(text: &str) -> Self {
        let re = command_regex();
        let mut commands = Vec::new();
        for captures in re.captures_iter(text) {
            let command_text = captures.get(1).unwrap().as_str();
            commands.push(Command::parse(command_text));
        }
        Document { commands }
    }
    pub fn reformat(text: &str) -> Cow<str> {
        let re = command_regex();
        re.replace_all(text, |captures: &Captures| {
            let command_text = captures.get(1).unwrap().as_str();
            format!(
                "> {}.",
                Command::parse(command_text)
                    .to_display_item()
                    .display_to_string()
            )
        })
    }
}

#[live_prop_test]
impl Command {
    #[live_prop_test(postcondition = "result.check_roundtrips()")]
    pub fn parse(text: &str) -> Self {
        let parser = CommandParser::new();
        match parser.parse(text) {
            Ok(command) => command,
            Err(e) => panic!("While parsing:\n    {text}\nGot error:\n    {e}"),
        }
    }
    fn check_roundtrips(&self) -> Result<(), String> {
        let text = self.to_string();
        let result = CommandParser::new().parse(&text).map_err(|e| {
            format!("Failed parsing generated text:\n    {text}\nWith error:\n    {e}")
        })?;
        lpt_assert_eq!(
            self,
            &result,
            "Roundtrip mismatch with generated text:\n    {text}"
        );
        let text = self.to_display_item().display_to_string();
        let result = CommandParser::new().parse(&text).map_err(|e| {
            format!("Failed parsing generated text:\n    {text}\nWith error:\n    {e}")
        })?;
        lpt_assert_eq!(
            self,
            &result,
            "Roundtrip mismatch with generated text:\n    {text}"
        );
        Ok(())
    }
}

#[test]
fn tests() {
    use AbstractionKind::*;
    use Command::*;
    use Formula::{Apply, Hole, Prop, Usage};
    let tests = [(
        "Foo := λP:ℙ, ∀p:P, (p _)",
        Assign(
            "Foo".to_owned(),
            Formula::Abstraction(Box::new(Abstraction {
                kind: Lambda,
                parameter_name: "P".to_string(),
                parameter_type: Prop,
                body: Formula::Abstraction(Box::new(Abstraction {
                    kind: ForAll,
                    parameter_name: "p".to_string(),
                    parameter_type: Usage("P".to_string()),
                    body: Apply(Box::new([Usage("p".to_string()), Hole])),
                })),
            })),
        ),
    )];
    for (text, command) in tests {
        assert_eq!(CommandParser::new().parse(text).unwrap(), command)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coc_text_format_1::metavariable_conversions::MetavariablesInjectionContext;
    use crate::metavariable::Environment;
    fn check_document(path: &str) {
        let document = Document::parse(&std::fs::read_to_string(path).unwrap());
        let mut environment = Environment::default();
        let mut injector = MetavariablesInjectionContext::for_environment(&mut environment);
        injector.inject_commands(&document.commands);
    }
    #[test]
    fn load_boxes() {
        check_document("data/boxes.coc_1");
    }
    #[test]
    fn load_inductive() {
        check_document("data/inductive_types.coc_1");
    }
}
