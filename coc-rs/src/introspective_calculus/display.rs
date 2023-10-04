use crate::introspective_calculus::{Atom, Formula};
use live_prop_test::live_prop_test;
use std::fmt::{Display, Formatter};

pub struct FormulaAsShorthand<'a>(&'a Formula);

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
