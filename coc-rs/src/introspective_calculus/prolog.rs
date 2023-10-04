use crate::display::DisplayItem;
use crate::introspective_calculus;
use crate::introspective_calculus::{Atom, Formula};
use live_prop_test::live_prop_test;
use std::fmt::{Display, Formatter, Write};
use std::path::Path;

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
                    Atom::EmptySet => "z",
                    Atom::Implies => "imp",
                    Atom::Union => "u",
                    Atom::Const => "c",
                    Atom::Fuse => "f",
                    Atom::All => "all",
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

pub fn knowledge_base(axioms_path: impl AsRef<Path>) -> String {
    let mut result = "istrue(B) :- istrue(A), istrue(a(a(a(imp,N),A),B)).\n".to_string();
    for axiom in introspective_calculus::all_axioms(axioms_path) {
        writeln!(
            result,
            "istrue({}).",
            axiom.conclusion.to_raw_with_metavariables().as_prolog()
        )
        .unwrap();
    }
    result
}
