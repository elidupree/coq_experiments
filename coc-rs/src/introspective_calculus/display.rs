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
                    Atom::Level0 => "z",
                    Atom::LevelSuccessor => "s",
                    Atom::Implies => "imp",
                    Atom::Equals => "eq",
                    Atom::InductionOnProofs => "induction_on_proofs",
                    Atom::Const => "c",
                    Atom::Fuse => "f",
                };
                write!(f, "{}", text)
            }
            Formula::Apply(g) => {
                write!(
                    f,
                    "({} {})",
                    FormulaAsShorthand(&g[0]),
                    FormulaAsShorthand(&g[1])
                )
            }
            _ => panic!("formula {:?} should already be raw", self.0),
        }
    }
}
