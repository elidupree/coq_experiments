use crate::introspective_calculus::proof_hierarchy::Proof;
use crate::introspective_calculus::raw_proofs::{CleanExternalRule, Rule, RuleTrait, ALL_AXIOMS};
use crate::introspective_calculus::raw_proofs_ext::ALL_AXIOM_SCHEMAS;
use crate::introspective_calculus::{Formula, RWMFormula, RWMFormulaValue, RawFormula};
use crate::utils::todo;
use crate::{formula, ic, substitutions};

pub trait FormulaProver {
    fn try_prove(&self, formula: RWMFormula) -> Result<Proof, String>;
}
// pub trait InferenceProver {
//     fn try_prove(&self, inference: Inference) -> Result<Proof, String>;
// }

impl RWMFormula {
    pub fn try_prove(&self, prover: impl FormulaProver) -> Result<Proof, String> {
        prover.try_prove(self.clone())
    }
    pub fn prove(&self, prover: impl FormulaProver) -> Proof {
        prover.try_prove(self.clone()).unwrap()
    }
}

impl Formula {
    pub fn try_prove(&self, prover: impl FormulaProver) -> Result<Proof, String> {
        self.to_rwm().try_prove(prover)
    }
    pub fn prove(&self, prover: impl FormulaProver) -> Proof {
        self.to_rwm().prove(prover)
    }
}

impl RawFormula {
    pub fn try_prove(&self, prover: impl FormulaProver) -> Result<Proof, String> {
        self.to_rwm().try_prove(prover)
    }
    pub fn prove(&self, prover: impl FormulaProver) -> Proof {
        self.to_rwm().prove(prover)
    }
}

#[derive(Copy, Clone)]
pub struct ByAssumingIt;
// #[derive(Copy, Clone)]
// pub struct BySpecializing<'a>(pub &'a Proof);
#[derive(Copy, Clone)]
pub struct ByAxiomSchema;
#[derive(Copy, Clone)]
pub struct BySpecializingAxiom;
#[derive(Copy, Clone)]
pub struct ByPartiallySpecializingAxiom;
#[derive(Copy, Clone)]
pub struct ByUnfolding;
#[derive(Copy, Clone)]
pub struct ByGeneralizedUnfolding;
#[derive(Copy, Clone)]
pub struct BySubstitutingWith<'a>(pub &'a [Proof]);
#[derive(Copy, Clone)]
pub struct ByScriptNamed<'a>(pub &'a str);
#[derive(Copy, Clone)]
pub struct ByScriptWithPremises<'a>(pub &'a str, pub &'a [Proof]);
#[derive(Copy, Clone)]
pub struct ByConvertingBothSides<'a, B>(pub &'a Proof, pub B);
pub struct ByIndistinguishability {
    pub equivalence: Proof,
    pub extractor: RWMFormula,
}
pub struct ByInternalIndistinguishability {
    pub equivalence: RWMFormula,
    pub extractor: RWMFormula,
}

impl FormulaProver for ByAssumingIt {
    fn try_prove(&self, formula: RWMFormula) -> Result<Proof, String> {
        Ok(Proof::by_premise(formula))
    }
}

impl FormulaProver for ByAxiomSchema {
    fn try_prove(&self, formula: RWMFormula) -> Result<Proof, String> {
        for a in ALL_AXIOM_SCHEMAS.iter() {
            if let Ok(s) = a.inference().conclusion.substitutions_to_become(&formula) {
                return Ok(Proof::by_rule(a.specialize(s), Vec::new()).unwrap());
            }
        }
        Err(format!("No axiom schema matched {formula}"))
    }
}

impl FormulaProver for BySpecializingAxiom {
    fn try_prove(&self, formula: RWMFormula) -> Result<Proof, String> {
        // let Some(formula) = formula.to_raw() else {
        //     return Err("Can't specialize axiom to non-raw formula".to_string());
        // };
        for axiom in ALL_AXIOMS.iter() {
            if let Ok(args) = axiom.internal_form.args_to_return(&formula) {
                return Ok(axiom.proof().specialize(&args));
            }
        }
        Err(format!("No axiom matched {formula}"))
    }
}

impl FormulaProver for ByPartiallySpecializingAxiom {
    fn try_prove(&self, formula: RWMFormula) -> Result<Proof, String> {
        let formula = formula
            .already_uncurried_function_equivalence()
            .map_err(|e| {
                format!("Can't specialize axiom to non-UCF: {e} \n\n(formula was {formula}")
            })?;
        for axiom in ALL_AXIOMS.iter() {
            //eprintln!("{}", axiom.internal_form);
            if let Ok(args) = axiom.internal_form.generalized_args_to_return(&formula) {
                return Ok(axiom.proof().partially_specialize(&args).proof().clone());
            }
        }
        Err(format!("No axiom matched {}", formula.formula()))
    }
}

impl FormulaProver for ByUnfolding {
    fn try_prove(&self, formula: RWMFormula) -> Result<Proof, String> {
        // TODO: be more efficient I guess?
        // TODO fix duplicate code ID 39483029345
        let [a, b] = formula
            .as_eq_sides()
            .unwrap()
            .map(|s| s.unfold_up_to_n_subformulas_proof(100));
        Proof::eq_trans_chain(&[a, b.flip_conclusion()])
    }
}

impl FormulaProver for ByGeneralizedUnfolding {
    fn try_prove(&self, formula: RWMFormula) -> Result<Proof, String> {
        // TODO: be more efficient I guess?
        // TODO fix duplicate code ID 39483029345
        let [a, b] = formula
            .as_eq_sides()
            .unwrap()
            .map(|s| s.generalized_unfold_up_to_n_subformulas_proof(100));
        Proof::eq_trans_chain(&[a, b.flip_conclusion()])
    }
}

impl<B: FormulaProver> FormulaProver for ByConvertingBothSides<'_, B> {
    fn try_prove(&self, formula: RWMFormula) -> Result<Proof, String> {
        let ByConvertingBothSides(premise, how) = self;
        let [a, b] = premise.conclusion().as_eq_sides().unwrap();
        let [c, d] = formula.as_eq_sides().unwrap();
        let l = how.try_prove(ic!(a = c).to_rwm())?;
        let r = how.try_prove(ic!(b = d).to_rwm())?;
        Ok(Proof::eq_trans_chain(&[l.flip_conclusion(), (*premise).clone(), r]).unwrap())
    }
}

impl FormulaProver for BySubstitutingWith<'_> {
    fn try_prove(&self, formula: RWMFormula) -> Result<Proof, String> {
        let equivalences = self.0;
        for equivalence in equivalences {
            if equivalence.conclusion() == formula {
                return Ok(equivalence.clone());
            }
            let e2 = equivalence.flip_conclusion();
            if e2.conclusion() == formula {
                return Ok(e2);
            }
        }
        let [a, b] = formula.as_eq_sides().unwrap();
        let [[af, ax], [bf, bx]] = [&a, &b]
            .try_map(|s| match s.value() {
                RWMFormulaValue::Apply(children) => Some(children),
                _ => None,
            })
            .ok_or_else(|| format!("could not equate `{a}` with `{b}`"))?;
        let fp = if af != bf {
            Some(
                Proof::by_rule(
                    Rule::from(CleanExternalRule::SubstituteInLhs)
                        .specialize(substitutions! {A: &af, B: &bf, C: &ax}),
                    vec![self.try_prove(ic!(af = bf).into())?],
                )
                .unwrap(),
            )
        } else {
            None
        };
        let xp = if ax != bx {
            Some(
                Proof::by_rule(
                    Rule::from(CleanExternalRule::SubstituteInRhs)
                        .specialize(substitutions! {A: &ax, B: &bx, C: &bf}),
                    vec![self.try_prove(ic!(ax = bx).into())?],
                )
                .unwrap(),
            )
        } else {
            None
        };
        match (fp, xp) {
            (None, None) => {
                Err("don't use BySubstitutionWith for eq_refl (this arbitrary restriction could be removed if there was a reason)".to_string())
            }
            (Some(p), None) | (None, Some(p)) => Ok(p),
            (Some(fp), Some(xp)) => {
                // af ax = bf ax ... bf ax = bf bx
                Ok(Proof::eq_trans_chain(&[fp, xp]).unwrap())
            }
        }
    }
}

impl FormulaProver for ByIndistinguishability {
    fn try_prove(&self, formula: RWMFormula) -> Result<Proof, String> {
        let [ca, cb] = self
            .equivalence
            .conclusion()
            .as_eq_sides()
            .unwrap()
            .map(|f| ic!({self.extractor} f));
        let ca_cb = ic!(ca = cb).prove(BySubstitutingWith(&[self.equivalence.clone()]));
        formula.try_prove(ByConvertingBothSides(&ca_cb, ByUnfolding))
    }
}

impl FormulaProver for ByInternalIndistinguishability {
    fn try_prove(&self, formula: RWMFormula) -> Result<Proof, String> {
        let c = &self.extractor;
        let [a, b] = self.equivalence.as_eq_sides().unwrap();
        let folded = formula!("(a=b) = (a=b & (c a = c b))", {a,b,c}).prove(BySpecializingAxiom);
        formula.try_prove(ByConvertingBothSides(&folded, ByUnfolding))
    }
}

impl FormulaProver for ByScriptNamed<'_> {
    fn try_prove(&self, formula: RWMFormula) -> Result<Proof, String> {
        todo(formula)
    }
}
impl FormulaProver for ByScriptWithPremises<'_> {
    fn try_prove(&self, formula: RWMFormula) -> Result<Proof, String> {
        todo(formula)
    }
}
