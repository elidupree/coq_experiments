#[allow(clippy::all)]
mod lalrpop_wrapper {
    use lalrpop_util::lalrpop_mod;
    lalrpop_mod!(pub(crate) coc_text_format_1, "/coc_text_format_1/coc_text_format_1.rs");
}

pub use self::lalrpop_wrapper::coc_text_format_1::CommandParser;
use crate::metavariable::{Environment, MetavariableId};
use regex::Regex;
use std::collections::HashMap;

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Command {
    Assign(String, Formula),
    ClaimType(Formula, Formula),
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum AbstractionKind {
    Lambda,
    ForAll,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Abstraction {
    kind: AbstractionKind,
    parameter_name: String,
    parameter_type: Formula,
    body: Formula,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Formula {
    Prop,
    Usage(String),
    Hole,
    Abstraction(Box<Abstraction>),
    Apply(Box<[Formula; 2]>),
}

pub struct Document {
    commands: Vec<Command>,
}

struct MetavariablesInjectionContext {
    existing_names: HashMap<String, Vec<MetavariableId>>,
    ids_by_complete_structure: HashMap<u128, Vec<MetavariableId>>,
    unused_ids_by_unshared_incomplete_structure: HashMap<u128, Vec<MetavariableId>>,
}

impl Document {
    pub fn parse(text: &str) -> Self {
        let re = Regex::new(r"(?m)^>([^\.]*)\.").unwrap();
        let parser = CommandParser::new();
        let mut commands = Vec::new();
        for captures in re.captures_iter(text) {
            let command_text = captures.get(1).unwrap().as_str();
            match parser.parse(command_text) {
                Ok(command) => commands.push(command),
                Err(e) => panic!("While parsing:\n    {command_text}\nGot error:\n    {e}"),
            }
        }
        Document { commands }
    }
    pub fn inject_as_metavariables(environment: &mut Environment) {
        let mut existing_names: HashMap<String, Vec<MetavariableId>> = HashMap::new();
        for metavariable in environment.metavariables() {
            existing_names
                .entry(metavariable.name().to_owned())
                .or_default()
                .push(metavariable.id());
        }
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
    #[test]
    fn load_boxes() {
        Document::parse(&std::fs::read_to_string("data/boxes.coc_1").unwrap());
    }
}
