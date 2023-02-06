#[allow(clippy::all)]
mod lalrpop_wrapper {
    use lalrpop_util::lalrpop_mod;
    lalrpop_mod!(pub(crate) coc_text_format_1, "/coc_text_format_1/coc_text_format_1.rs");
}

pub use self::lalrpop_wrapper::coc_text_format_1::CommandParser;
use crate::metavariable::{Environment, MetavariableId};
use live_prop_test::{live_prop_test, lpt_assert_eq};
use regex::Regex;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

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
        let mut commands = Vec::new();
        for captures in re.captures_iter(text) {
            let command_text = captures.get(1).unwrap().as_str();
            commands.push(Command::parse(command_text));
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

#[live_prop_test]
impl Command {
    #[live_prop_test(postcondition = "result.check_roundtrip()")]
    pub fn parse(text: &str) -> Self {
        let parser = CommandParser::new();
        match parser.parse(text) {
            Ok(command) => command,
            Err(e) => panic!("While parsing:\n    {text}\nGot error:\n    {e}"),
        }
    }
    fn check_roundtrip(&self) -> Result<(), String> {
        let text = self.to_string();
        let result = CommandParser::new()
            .parse(&text)
            .map_err(|e| e.to_string())?;
        lpt_assert_eq!(self, &result);
        Ok(())
    }
}

impl Display for Command {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Command::Assign(name, formula) => {
                write!(f, "{name} := {formula}")
            }
            Command::ClaimType(value_formula, type_formula) => {
                write!(f, "{value_formula} : {type_formula}")
            }
        }
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Formula::Prop => {
                write!(f, "ℙ")
            }
            Formula::Usage(name) => {
                write!(f, "{name}")
            }
            Formula::Hole => {
                write!(f, "_")
            }
            Formula::Abstraction(abstraction) => {
                let Abstraction {
                    kind,
                    parameter_name,
                    parameter_type,
                    body,
                } = &**abstraction;
                write!(f, "{kind}{parameter_name}:{parameter_type}, {body}")
            }
            Formula::Apply(children) => {
                let mut chain_members = vec![&children[1]];
                let mut walker = &children[0];
                while let Formula::Apply(cx) = walker {
                    chain_members.push(&cx[1]);
                    walker = &cx[0];
                }
                chain_members.push(walker);
                write!(f, "(")?;
                for (index, member) in chain_members.into_iter().enumerate().rev() {
                    if matches!(member, Formula::Abstraction(_)) {
                        write!(f, "({member})")?;
                    } else {
                        write!(f, "{member}")?;
                    }
                    if index != 0 {
                        write!(f, " ")?;
                    }
                }
                write!(f, ")")?;
                Ok(())
            }
        }
    }
}

impl Display for AbstractionKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            AbstractionKind::Lambda => {
                write!(f, "λ")
            }
            AbstractionKind::ForAll => {
                write!(f, "∀")
            }
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
