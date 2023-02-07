use crate::coc_text_format_1::{Abstraction, AbstractionKind, Command, Document, Formula};
use std::fmt::{Display, Formatter, Write};
use std::{fmt, iter};

pub(super) trait DisplayItem {
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
        writer.write_str(self)
    }

    fn display_with_splits(&self, _prior_indentation: usize, writer: &mut String) -> fmt::Result {
        writer.write_str(self)
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
    pub(super) fn to_display_item(&self) -> Box<dyn DisplayItem> {
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
    pub(super) fn to_display_item(&self, parenthesize_abstractions: bool) -> Box<dyn DisplayItem> {
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

impl Display for Document {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut last = None;
        for command in &self.commands {
            if last.is_some() && matches!(command, Command::ClaimType(_, _)) {
                writeln!(f)?;
            }
            writeln!(f, "> {}.", command.to_display_item().display_to_string())?;
            last = Some(command);
        }
        Ok(())
    }
}
