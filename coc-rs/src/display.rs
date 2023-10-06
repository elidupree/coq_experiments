use std::fmt;
use std::fmt::{Display, Formatter, Write};

#[derive(Copy, Clone)]
pub enum DisplayAttemptKind {
    OneLiner,
    WithSplits { prior_indentation: usize },
}

pub trait DisplayItem {
    fn try_display(&self, writer: &mut dyn Write, kind: DisplayAttemptKind) -> fmt::Result;
    fn display_with_splits_if_needed(
        &self,
        item_length_limit: usize,
        current_indentation: usize,
        writer: &mut dyn Write,
    ) -> fmt::Result {
        let mut one_liner = LimitedLengthString::new(item_length_limit);
        match self.try_display(&mut one_liner, DisplayAttemptKind::OneLiner) {
            Ok(_) => writer.write_str(&one_liner.data),
            Err(_) => self.try_display(
                writer,
                DisplayAttemptKind::WithSplits {
                    prior_indentation: current_indentation,
                },
            ),
        }
    }
    fn display(&self) -> Box<dyn Display + '_> {
        Box::new(DisplayDisplayItem(self))
    }
    fn to_string(&self) -> String {
        self.display().to_string()
    }
}

pub struct DisplayDisplayItem<'a, T: ?Sized>(&'a T);

impl<'a, T: DisplayItem + ?Sized> Display for DisplayDisplayItem<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.0.display_with_splits_if_needed(80, 2, f)
    }
}

pub struct LimitedLengthString {
    pub data: String,
    pub characters_remaining: usize,
}
impl LimitedLengthString {
    pub fn new(characters_remaining: usize) -> Self {
        LimitedLengthString {
            data: String::new(),
            characters_remaining,
        }
    }
}

impl Write for LimitedLengthString {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.characters_remaining = self
            .characters_remaining
            .checked_sub(s.chars().count())
            .ok_or(fmt::Error)?;
        self.data.write_str(s)
    }
}

pub struct DisplayItemSequence {
    pub always_parens: bool,
    pub items: Vec<Box<dyn DisplayItem>>,
}

impl DisplayItem for DisplayItemSequence {
    fn try_display(&self, writer: &mut dyn Write, kind: DisplayAttemptKind) -> fmt::Result {
        match kind {
            DisplayAttemptKind::OneLiner => {
                if self.always_parens {
                    write!(writer, "(")?;
                }
                for (index, item) in self.items.iter().enumerate() {
                    item.try_display(writer, DisplayAttemptKind::OneLiner)?;
                    if index + 1 != self.items.len() {
                        write!(writer, " ")?;
                    }
                }
                if self.always_parens {
                    write!(writer, ")")?;
                }
            }
            DisplayAttemptKind::WithSplits { prior_indentation } => {
                write!(writer, "(")?;
                let indent = " ".repeat(prior_indentation);
                let item_length_limit = 30.max(77 - prior_indentation);
                for item in &self.items {
                    write!(writer, "\n{}  ", indent)?;
                    item.display_with_splits_if_needed(
                        item_length_limit,
                        prior_indentation + 2,
                        writer,
                    )?;
                }
                write!(writer, "\n{})", indent)?;
            }
        }

        Ok(())
    }
}

impl DisplayItem for &str {
    fn try_display(&self, writer: &mut dyn Write, _kind: DisplayAttemptKind) -> fmt::Result {
        writer.write_str(self)
    }
}

impl DisplayItem for String {
    fn try_display(&self, writer: &mut dyn Write, _kind: DisplayAttemptKind) -> fmt::Result {
        writer.write_str(self)
    }
}