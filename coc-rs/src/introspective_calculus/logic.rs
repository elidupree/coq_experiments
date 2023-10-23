pub use self::proof_verifier::TrueFormula;
use crate::ic;
use crate::introspective_calculus::{Formula, PROP_TRUE};

mod proof_verifier {
    use crate::ic;
    use crate::introspective_calculus::Formula;
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
            let [a2, b] = a_equals_b.as_eq_sides()?;
            (*a2 == *a.as_raw_with_metavariables()).then(|| TrueFormula {
                formula: b.clone(),
                used_axioms: a_equals_b
                    .used_axioms
                    .union(&a.used_axioms)
                    .cloned()
                    .collect(),
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
            let [a, b] = a_equals_b.as_eq_sides()?;
            Some(TrueFormula {
                formula: ic!((a c) = (b c)),
                used_axioms: a_equals_b.used_axioms.clone(),
            })
        }
        pub fn compatibility_right(c: Formula, a_equals_b: &TrueFormula) -> Option<TrueFormula> {
            let [a, b] = a_equals_b.as_eq_sides()?;
            Some(TrueFormula {
                formula: ic!((c a) = (c b)),
                used_axioms: a_equals_b.used_axioms.clone(),
            })
        }

        pub fn formula(&self) -> &Formula {
            &self.formula
        }
        pub fn used_axioms(&self) -> &HashSet<Formula> {
            &self.used_axioms
        }
    }
}

impl TrueFormula {
    pub fn eq_refl(formula: Formula) -> TrueFormula {
        let a = TrueFormula::definition_of_const(formula.clone(), Formula::default());
        let b = TrueFormula::compatibility_right(ic!(equals), &a).unwrap();
        let c = TrueFormula::compatibility_left(&b, formula).unwrap();
        TrueFormula::substitute_whole_formula(&c, &a).unwrap()
    }
    pub fn prop_true() -> TrueFormula {
        TrueFormula::eq_refl(ic!(equals))
    }
    pub fn eq_sym(a_equals_b: &TrueFormula) -> Option<TrueFormula> {
        let [a, _b] = a_equals_b.as_eq_sides()?;
        let a_equals_a = TrueFormula::eq_refl(a.clone());
        let eqa_equals_eqb = TrueFormula::compatibility_right(ic!(equals), a_equals_b).unwrap();
        let eqaa_equals_eqba = TrueFormula::compatibility_left(&eqa_equals_eqb, a.clone()).unwrap();
        Some(TrueFormula::substitute_whole_formula(&eqaa_equals_eqba, &a_equals_a).unwrap())
    }
    pub fn specialize(universal_truth: &TrueFormula, argument: Formula) -> Option<TrueFormula> {
        let [ct, _p] = universal_truth.as_eq_sides()?;
        if ct.as_raw_with_metavariables() != ic!(const PROP_TRUE).as_raw_with_metavariables() {
            return None;
        }
        let cta_equals_pa =
            TrueFormula::compatibility_left(universal_truth, argument.clone()).unwrap();
        let cta_equals_true = TrueFormula::definition_of_const(Formula::prop_true(), argument);
        let true_equals_cta = TrueFormula::eq_sym(&cta_equals_true).unwrap();
        let cta =
            TrueFormula::substitute_whole_formula(&true_equals_cta, &TrueFormula::prop_true())
                .unwrap();
        Some(TrueFormula::substitute_whole_formula(&cta_equals_pa, &cta).unwrap())
    }
}
