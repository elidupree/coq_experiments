use crate::display::{
    DisplayItem, DisplayItemSequence, WithUnsplittablePrefix, WithUnsplittableSuffix,
};
use crate::introspective_calculus::uncurried_function::{
    UncurriedFunction, UncurriedFunctionEquivalence, UncurriedFunctionValue,
};
use crate::introspective_calculus::{
    AbstractionKind, Atom, Formula, FormulaValue, RWMFormula, RawFormula, Substitutions, ID,
};
use itertools::Itertools;
use live_prop_test::live_prop_test;
use std::fmt::{Display, Formatter};

pub struct FormulaAsShorthand<'a>(&'a Formula);

impl Display for Atom {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Atom::Equals => "equals".fmt(f),
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
        match &self.0.value {
            FormulaValue::Metavariable(name) => {
                write!(f, "{}", name)
            }
            FormulaValue::Atom(a) => {
                let text = match a {
                    Atom::Equals => "e",
                    Atom::Const => "c",
                    Atom::Fuse => "f",
                };
                write!(f, "{}", text)
            }
            FormulaValue::Apply(g) => {
                let mut stack = vec![g];
                write!(f, "(")?;
                while let FormulaValue::Apply(next) = &stack.last().unwrap()[0].value {
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
    pub fn to_display_item(&self, parenthesize_abstractions: bool) -> Box<dyn DisplayItem> {
        match &self.value {
            FormulaValue::Atom(a) => Box::new(a.to_string()),
            FormulaValue::Metavariable(name) => Box::new(name.clone()),
            FormulaValue::NamedGlobal { name, .. } => Box::new(name.clone()),
            FormulaValue::And(children) => {
                let mut stack = vec![&children[1], &children[0]];
                let mut items = Vec::with_capacity(2);
                while let Some(next) = stack.pop() {
                    if let FormulaValue::And(children2) = &next.value {
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
                            Box::new(WithUnsplittablePrefix::new("& ", f.to_display_item(true)))
                        }))
                        .collect(),
                })
            }
            FormulaValue::Equals(children) => Box::new(DisplayItemSequence {
                always_parens: true,
                items: vec![
                    children[0].to_display_item(true),
                    Box::new(WithUnsplittablePrefix::new(
                        "= ",
                        children[1].to_display_item(true),
                    )),
                ],
            }),
            FormulaValue::Implies(children) => Box::new(DisplayItemSequence {
                always_parens: true,
                items: vec![
                    children[0].to_display_item(true),
                    Box::new(WithUnsplittablePrefix::new(
                        "-> ",
                        children[1].to_display_item(true),
                    )),
                ],
            }),
            FormulaValue::Tuple(children) => Box::new(DisplayItemSequence {
                always_parens: true,
                items: children
                    .iter()
                    .enumerate()
                    .map(|(i, child)| {
                        let unmarked = child.to_display_item(true);
                        if i + 1 < children.len() || children.len() <= 1 {
                            Box::new(WithUnsplittableSuffix::new(",", unmarked))
                        } else {
                            unmarked
                        }
                    })
                    .collect(),
            }),
            FormulaValue::NameAbstraction(kind, name, body) => {
                let mut chain_members = vec![(kind, name)];
                let mut walker = body;
                while let FormulaValue::NameAbstraction(kind2, name2, body2) = &walker.value {
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
            FormulaValue::Apply(children) => {
                if self.to_rwm() == ID.to_rwm() {
                    return ID.to_display_item(parenthesize_abstractions);
                }
                let mut chain_members = vec![&children[1]];
                let mut walker = &children[0];
                while let FormulaValue::Apply(cx) = &walker.value {
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

impl UncurriedFunction {
    pub fn to_display_item(&self, _parenthesize_abstractions: bool) -> Box<dyn DisplayItem> {
        match &self.value() {
            UncurriedFunctionValue::Constant(f) => Box::new(DisplayItemSequence {
                always_parens: true,
                items: vec![
                    /*Box::new("const".to_string()), */ f.to_display_item(true),
                ],
            }),
            UncurriedFunctionValue::PopIn(child) => {
                let mut pops = 1;
                let mut walker = child;
                while let UncurriedFunctionValue::PopIn(c2) = walker.value() {
                    walker = c2;
                    pops += 1;
                }
                if *walker == UncurriedFunction::top() {
                    Box::new(format!("{pops}"))
                } else {
                    Box::new(DisplayItemSequence {
                        always_parens: true,
                        items: vec![Box::new("^{pops}".to_string()), child.to_display_item(true)],
                    })
                }
            }
            UncurriedFunctionValue::Top => Box::new("0".to_string()),
            UncurriedFunctionValue::Apply(children) => {
                let mut chain_members = vec![&children[1]];
                let mut walker = &children[0];
                while let UncurriedFunctionValue::Apply(cx) = walker.value() {
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
impl UncurriedFunctionEquivalence {
    pub fn to_display_item(&self, _parenthesize_abstractions: bool) -> Box<dyn DisplayItem> {
        Box::new(DisplayItemSequence {
            always_parens: true,
            items: vec![
                self.sides[0].to_display_item(true),
                Box::new(WithUnsplittablePrefix::new(
                    "= ",
                    self.sides[1].to_display_item(true),
                )),
            ],
        })
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.to_display_item(false).display().fmt(f)
    }
}

impl Display for UncurriedFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.to_display_item(false).display().fmt(f)
    }
}

impl Display for UncurriedFunctionEquivalence {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.to_display_item(false).display().fmt(f)
    }
}

impl Display for RWMFormula {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Display for RawFormula {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::fmt::Debug for Formula {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl std::fmt::Debug for RWMFormula {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl std::fmt::Debug for RawFormula {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

pub fn format_substitutions(substitutions: &Substitutions) -> String {
    format!(
        "{{ {} }}",
        substitutions
            .iter()
            .map(|(k, v)| format!("{k} := {v}"))
            .join(", ")
    )
}
