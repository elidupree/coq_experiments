use crate::introspective_calculus::{Atom, Formula};
use live_prop_test::live_prop_test;
use std::fmt::{Display, Formatter};

pub struct FormulaAsProlog<'a>(&'a Formula);

#[live_prop_test]
impl Formula {
    #[live_prop_test(precondition = "self.is_raw_with_metavariables()")]
    pub fn as_prolog(&self) -> FormulaAsProlog {
        FormulaAsProlog(self)
    }
}

impl Display for FormulaAsProlog<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Formula::Metavariable(name) => {
                // make sure it always starts with a capital letter, to count as a Prolog variable
                write!(f, "V{}", name)
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
                    "a({},{})",
                    FormulaAsProlog(&g[0]),
                    FormulaAsProlog(&g[1])
                )
            }
            _ => panic!("formula {:?} should already be raw", self.0),
        }
    }
}
