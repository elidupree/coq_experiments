use crate::coc_text_format_1::{Abstraction, AbstractionKind, Command, Document, Formula};
use crate::display::{DisplayAttemptKind, DisplayItem, DisplayItemSequence};
use std::fmt::{Display, Formatter, Write};
use std::{fmt, iter};

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
    fn try_display(&self, writer: &mut dyn Write, attempt_kind: DisplayAttemptKind) -> fmt::Result {
        let AbstractionParameterItem {
            kind,
            parameter_name,
            parameter_type,
        } = self;
        write!(writer, "{kind}{parameter_name}:")?;
        parameter_type.try_display(writer, attempt_kind)?;
        write!(writer, ",")?;
        Ok(())
    }
}

impl DisplayItem for CommandItem {
    fn try_display(&self, writer: &mut dyn Write, kind: DisplayAttemptKind) -> fmt::Result {
        write!(writer, "{}", self.prefix)?;
        self.formula.try_display(writer, kind)
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
            writeln!(f, "> {}.", command.to_display_item().display())?;
            last = Some(command);
        }
        Ok(())
    }
}
