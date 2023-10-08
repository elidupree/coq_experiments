use crate::display::{DisplayItem, DisplayItemSequence, WithUnsplittablePrefix};
use crate::introspective_calculus::{AbstractionKind, Atom, Formula};
use live_prop_test::live_prop_test;
use std::fmt::{Display, Formatter};

pub struct FormulaAsShorthand<'a>(&'a Formula);

impl Display for Atom {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Atom::Implies => "implies".fmt(f),
            Atom::EmptySet => "empty_set".fmt(f),
            Atom::Union => "union".fmt(f),
            Atom::All => "all".fmt(f),
            Atom::Const => "const".fmt(f),
            Atom::Fuse => "fuse".fmt(f),
        }
    }
}

#[live_prop_test]
impl Formula {
    #[live_prop_test(precondition = "self.is_raw_with_metavariables()")]
    pub fn as_shorthand(&self) -> FormulaAsShorthand {
        FormulaAsShorthand(self)
    }
}

impl Display for FormulaAsShorthand<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Formula::Metavariable(name) => {
                write!(f, "{}", name)
            }
            Formula::Atom(a) => {
                let text = match a {
                    Atom::EmptySet => "0",
                    Atom::Implies => "imp",
                    Atom::Union => "u",
                    Atom::Const => "c",
                    Atom::Fuse => "f",
                    Atom::All => "all",
                };
                write!(f, "{}", text)
            }
            Formula::Apply(g) => {
                let mut stack = vec![g];
                write!(f, "(")?;
                while let Formula::Apply(next) = &stack.last().unwrap()[0] {
                    stack.push(next);
                }
                write!(f, "{}", FormulaAsShorthand(&stack.last().unwrap()[0]))?;
                for h in stack.iter().rev() {
                    write!(f, " {}", FormulaAsShorthand(&h[1]))?;
                }
                write!(f, ")")?;
                Ok(())
            }
            _ => panic!("formula {:?} should already be raw", self.0),
        }
    }
}

impl Formula {
    pub(super) fn to_display_item(&self, parenthesize_abstractions: bool) -> Box<dyn DisplayItem> {
        match self {
            Formula::Atom(a) => Box::new(a.to_string()),
            Formula::Id => Box::new("id".to_string()),
            Formula::EmptySet => Box::new("∅".to_string()),
            Formula::Metavariable(name) => Box::new(name.clone()),
            Formula::Implies(children) => Box::new(DisplayItemSequence {
                always_parens: true,
                items: vec![
                    children[0].to_display_item(true),
                    Box::new(WithUnsplittablePrefix::new(
                        "-> ",
                        children[1].to_display_item(true),
                    )),
                ],
            }),
            Formula::Union(children) => {
                let mut stack = vec![&children[1], &children[0]];
                let mut items = Vec::with_capacity(2);
                while let Some(next) = stack.pop() {
                    if let Formula::Union(children2) = next {
                        stack.push(&children2[1]);
                        stack.push(&children2[0]);
                    } else {
                        items.push(next);
                    }
                }
                let (first, rest) = items.split_first().unwrap();
                Box::new(DisplayItemSequence {
                    always_parens: true,
                    items: std::iter::once(first.to_display_item(true))
                        .chain(rest.iter().map(|f| -> Box<dyn DisplayItem> {
                            Box::new(WithUnsplittablePrefix::new("∪ ", f.to_display_item(true)))
                        }))
                        .collect(),
                })
            }
            Formula::NameAbstraction(kind, name, body) => {
                let mut chain_members = vec![(kind, name)];
                let mut walker = body;
                while let Formula::NameAbstraction(kind2, name2, body2) = &**walker {
                    if kind2 != kind {
                        break;
                    }
                    chain_members.push((kind2, name2));
                    walker = body2;
                }
                let items = chain_members
                    .into_iter()
                    .map(|(k, n)| -> Box<dyn DisplayItem> {
                        Box::new(match k {
                            AbstractionKind::Lambda => {
                                format!("{n} =>")
                            }
                            AbstractionKind::ForAll => {
                                format!("∀{n},")
                            }
                        })
                    })
                    .chain(std::iter::once(walker.to_display_item(false)))
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

impl Display for Formula {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.to_display_item(false).display().fmt(f)
    }
}
