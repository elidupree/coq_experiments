use crate::introspective_calculus;
use crate::introspective_calculus::{Atom, Formula, FormulaValue};
use live_prop_test::live_prop_test;
use std::fmt::{Display, Formatter, Write};

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
        match &self.0.value {
            FormulaValue::Metavariable(name) => {
                // make sure it always starts with a capital letter, to count as a Prolog variable
                write!(f, "V{}", name)
            }
            FormulaValue::Atom(a) => {
                let text = match a {
                    Atom::And => "a",
                    Atom::Equals => "e",
                    Atom::Const => "c",
                    Atom::Fuse => "f",
                };
                write!(f, "{}", text)
            }
            FormulaValue::Apply(g) => {
                write!(
                    f,
                    "y({},{})",
                    FormulaAsProlog(&g[0]),
                    FormulaAsProlog(&g[1])
                )
            }
            _ => panic!("formula {:?} should already be raw", self.0),
        }
    }
}

pub fn knowledge_base() -> String {
    let mut result = "istrue(B) :- istrue(A), istrue(a(a(a(imp,N),A),B)).\n".to_string();
    for rule in introspective_calculus::all_official_rules() {
        writeln!(
            result,
            "istrue({}).",
            rule.formula.to_raw_with_metavariables().as_prolog()
        )
        .unwrap();
    }
    result
}
