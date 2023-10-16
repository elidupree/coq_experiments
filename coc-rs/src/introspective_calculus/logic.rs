use crate::introspective_calculus::Formula;
use crate::{ic, match_ic};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::ops::Deref;

#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct TrueFormula {
    formula: Formula,
    used_axioms: HashSet<Formula>,
}

impl Deref for TrueFormula {
    type Target = Formula;

    fn deref(&self) -> &Self::Target {
        &self.formula
    }
}

impl TrueFormula {
    pub fn axiom(formula: Formula) -> TrueFormula {
        TrueFormula {
            formula: formula.clone(),
            used_axioms: [formula].into_iter().collect(),
        }
    }
    pub fn substitute_whole_formula(
        a_equals_b: &TrueFormula,
        a: &TrueFormula,
    ) -> Option<TrueFormula> {
        match_ic!(a_equals_b.as_raw_with_metavariables(), {
            //TODO reduce duplicate code ID 3894475843
            ((equals a2) b) => (*a2 == *a.as_raw_with_metavariables()).then(||
                TrueFormula {
                    formula: b.clone(),
                    used_axioms: a_equals_b.used_axioms.union(&a.used_axioms).cloned().collect(),
                }),
            //TODO reduce duplicate code ID 3894475843
            (a2 = b) => (*a2 == *a.as_raw_with_metavariables()).then(||
                TrueFormula {
                    formula: b.clone(),
                    used_axioms: a_equals_b.used_axioms.union(&a.used_axioms).cloned().collect(),
                }),
            _ => None,
        })
    }
    pub fn definition_of_const(a: Formula, b: Formula) -> TrueFormula {
        TrueFormula {
            formula: ic!(((const a) b) = a),
            used_axioms: HashSet::new(),
        }
    }
    pub fn definition_of_fuse(a: Formula, b: Formula, c: Formula) -> TrueFormula {
        TrueFormula {
            formula: ic!((((fuse a) b) c) = ((a c) (b c))),
            used_axioms: HashSet::new(),
        }
    }
    pub fn compatibility_left(a_equals_b: &TrueFormula, c: Formula) -> Option<TrueFormula> {
        match_ic!(a_equals_b.as_raw_with_metavariables(), {
            //TODO reduce duplicate code ID 3894475843
            ((equals a) b) => Some(TrueFormula{
                formula: ic!((a c) = (b c)),
                used_axioms: a_equals_b.used_axioms.clone(),
            }),
            //TODO reduce duplicate code ID 3894475843
            (a = b) => Some(TrueFormula{
                formula: ic!((a c) = (b c)),
                used_axioms: a_equals_b.used_axioms.clone(),
            }),
            _ => None,
        })
    }
    pub fn compatibility_right(a_equals_b: &TrueFormula, c: Formula) -> Option<TrueFormula> {
        match_ic!(a_equals_b, {
            //TODO reduce duplicate code ID 3894475843
            ((equals a) b) => Some(TrueFormula{
                formula: ic!((c a) = (c b)),
                used_axioms: a_equals_b.used_axioms.clone(),
            }),
            //TODO reduce duplicate code ID 3894475843
            (a = b) => Some(TrueFormula{
                formula: ic!((c a) = (c b)),
                used_axioms: a_equals_b.used_axioms.clone(),
            }),
            _ => None,
        })
    }

    pub fn formula(&self) -> &Formula {
        &self.formula
    }
    pub fn used_axioms(&self) -> &HashSet<Formula> {
        &self.used_axioms
    }
}
