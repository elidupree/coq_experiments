#[allow(clippy::all)]
mod lalrpop_wrapper {
    use lalrpop_util::lalrpop_mod;
    lalrpop_mod!(pub(crate) coc_text_format_1, "/coc_text_format_1/coc_text_format_1.rs");
}

pub use self::lalrpop_wrapper::coc_text_format_1::CommandParser;
use crate::metavariable::{Environment, MetavariableId};
use live_prop_test::{live_prop_test, lpt_assert_eq};
use regex::{Captures, Regex};
use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt::{Display, Formatter, Write};
use std::{fmt, iter};

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Command {
    Assign(String, Formula),
    ClaimType(String, Formula),
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

trait DisplayItem {
    fn try_one_liner(&self, writer: &mut dyn fmt::Write) -> fmt::Result;
    fn display_with_splits(&self, prior_indentation: usize, writer: &mut String) -> fmt::Result;
    fn display_with_splits_if_needed(
        &self,
        item_length_limit: usize,
        current_indentation: usize,
        writer: &mut String,
    ) -> fmt::Result {
        let old_length = writer.len();
        let one_liner_result = self.try_one_liner(&mut LimitedLengthString {
            target: writer,
            characters_remaining: item_length_limit,
        });
        if one_liner_result.is_err() {
            writer.truncate(old_length);
            self.display_with_splits(current_indentation, writer)?;
        }
        Ok(())
    }
    fn display_to_string(&self) -> String {
        let mut result = String::new();
        self.display_with_splits_if_needed(80, 2, &mut result)
            .unwrap();
        result
    }
}

struct LimitedLengthString<'a> {
    target: &'a mut String,
    characters_remaining: usize,
}

impl Write for LimitedLengthString<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.characters_remaining = self
            .characters_remaining
            .checked_sub(s.chars().count())
            .ok_or(fmt::Error)?;
        self.target.write_str(s)
    }
}

struct DisplayItemSequence {
    always_parens: bool,
    items: Vec<Box<dyn DisplayItem>>,
}
impl DisplayItem for DisplayItemSequence {
    fn try_one_liner(&self, writer: &mut dyn Write) -> fmt::Result {
        if self.always_parens {
            write!(writer, "(")?;
        }
        for (index, item) in self.items.iter().enumerate() {
            item.try_one_liner(writer)?;
            if index + 1 != self.items.len() {
                write!(writer, " ")?;
            }
        }
        if self.always_parens {
            write!(writer, ")")?;
        }
        Ok(())
    }
    fn display_with_splits(&self, prior_indentation: usize, writer: &mut String) -> fmt::Result {
        write!(writer, "(")?;
        let indent = " ".repeat(prior_indentation);
        let item_length_limit = 30.max(77 - prior_indentation);
        for item in &self.items {
            write!(writer, "\n{}  ", indent)?;
            item.display_with_splits_if_needed(item_length_limit, prior_indentation + 2, writer)?;
        }
        write!(writer, "\n{})", indent)?;
        Ok(())
    }
}
impl DisplayItem for &str {
    fn try_one_liner(&self, writer: &mut dyn Write) -> fmt::Result {
        writer.write_str(self)
    }

    fn display_with_splits(&self, _prior_indentation: usize, writer: &mut String) -> fmt::Result {
        writer.write_str(self)
    }
}
impl DisplayItem for String {
    fn try_one_liner(&self, writer: &mut dyn Write) -> fmt::Result {
        writer.write_str(&self)
    }

    fn display_with_splits(&self, _prior_indentation: usize, writer: &mut String) -> fmt::Result {
        writer.write_str(&self)
    }
}

struct AbstractionParameterItem {
    kind: AbstractionKind,
    parameter_name: String,
    parameter_type: Box<dyn DisplayItem>,
}

struct CommandItem {
    prefix: String,
    formula: Box<dyn DisplayItem>,
}

impl DisplayItem for AbstractionParameterItem {
    fn try_one_liner(&self, writer: &mut dyn Write) -> fmt::Result {
        let AbstractionParameterItem {
            kind,
            parameter_name,
            parameter_type,
        } = self;
        write!(writer, "{kind}{parameter_name}:")?;
        parameter_type.try_one_liner(writer)?;
        write!(writer, ",")?;
        Ok(())
    }

    fn display_with_splits(&self, prior_indentation: usize, writer: &mut String) -> fmt::Result {
        let AbstractionParameterItem {
            kind,
            parameter_name,
            parameter_type,
        } = self;
        write!(writer, "{kind}{parameter_name}:")?;
        parameter_type.display_with_splits(prior_indentation, writer)?;
        write!(writer, ",")?;
        Ok(())
    }
}

impl DisplayItem for CommandItem {
    fn try_one_liner(&self, writer: &mut dyn Write) -> fmt::Result {
        write!(writer, "{}", self.prefix)?;
        self.formula.try_one_liner(writer)
    }

    fn display_with_splits(&self, prior_indentation: usize, writer: &mut String) -> fmt::Result {
        write!(writer, "{}", self.prefix)?;
        self.formula.display_with_splits(prior_indentation, writer)
    }
}
impl Command {
    fn to_display_item(&self) -> Box<dyn DisplayItem> {
        let (prefix, formula) = match self {
            Command::Assign(name, formula) => (format!("{name} := "), formula),
            Command::ClaimType(name, formula) => (format!("{name} : "), formula),
        };
        Box::new(CommandItem {
            prefix,
            formula: formula.to_display_item(false),
        })
    }
}

impl Formula {
    fn to_display_item(&self, parenthesize_abstractions: bool) -> Box<dyn DisplayItem> {
        match self {
            Formula::Prop => Box::new("ℙ"),
            Formula::Usage(name) => Box::new(name.clone()),
            Formula::Hole => Box::new("_"),
            Formula::Abstraction(abstraction) => {
                let mut chain_members = vec![abstraction];
                let mut walker = &abstraction.body;
                while let Formula::Abstraction(a) = walker {
                    if a.kind != abstraction.kind {
                        break;
                    }
                    chain_members.push(a);
                    walker = &a.body;
                }
                let items = chain_members
                    .into_iter()
                    .map(|a| -> Box<dyn DisplayItem> {
                        Box::new(AbstractionParameterItem {
                            kind: a.kind,
                            parameter_name: a.parameter_name.clone(),
                            parameter_type: a.parameter_type.to_display_item(true),
                        })
                    })
                    .chain(iter::once(walker.to_display_item(false)))
                    .collect();
                Box::new(DisplayItemSequence {
                    always_parens: parenthesize_abstractions,
                    items,
                })
            }
            Formula::Apply(children) => {
                let mut chain_members = vec![&children[1]];
                let mut walker = &children[0];
                while let Formula::Apply(cx) = walker {
                    chain_members.push(&cx[1]);
                    walker = &cx[0];
                }
                chain_members.push(walker);
                Box::new(DisplayItemSequence {
                    always_parens: true,
                    items: chain_members
                        .into_iter()
                        .rev()
                        .map(|f| f.to_display_item(true))
                        .collect(),
                })
            }
        }
    }
}

impl Display for Command {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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
    #[test]
    fn load_inductive() {
        Document::parse(&std::fs::read_to_string("data/inductive_types.coc_1").unwrap());
    }
}
