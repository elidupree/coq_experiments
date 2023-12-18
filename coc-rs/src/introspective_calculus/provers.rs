use crate::introspective_calculus::inference::Inference;
use crate::introspective_calculus::proof_hierarchy::ProofWithVariables;
use crate::introspective_calculus::raw_proofs::{CleanExternalRule, Rule, RuleTrait, ALL_AXIOMS};
use crate::introspective_calculus::raw_proofs_ext::ALL_AXIOM_SCHEMAS;
use crate::introspective_calculus::uncurried_function::UncurriedFunctionEquivalence;
use crate::introspective_calculus::{Formula, RWMFormula, RWMFormulaValue, RawFormula};
use crate::utils::todo;
use crate::{ic, substitutions};

pub trait FormulaProver {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String>;
}
// pub trait InferenceProver {
//     fn try_prove(&self, inference: Inference) -> Result<ProofWithPremises, String>;
// }

impl RWMFormula {
    pub fn try_prove(&self, prover: impl FormulaProver) -> Result<ProofWithVariables, String> {
        prover.try_prove(self.clone())
    }
    pub fn prove(&self, prover: impl FormulaProver) -> ProofWithVariables {
        prover.try_prove(self.clone()).unwrap()
    }
}

impl Formula {
    pub fn try_prove(&self, prover: impl FormulaProver) -> Result<ProofWithVariables, String> {
        self.to_rwm().try_prove(prover)
    }
    pub fn prove(&self, prover: impl FormulaProver) -> ProofWithVariables {
        self.to_rwm().prove(prover)
    }
}

impl RawFormula {
    pub fn try_prove(&self, prover: impl FormulaProver) -> Result<ProofWithVariables, String> {
        self.to_rwm().try_prove(prover)
    }
    pub fn prove(&self, prover: impl FormulaProver) -> ProofWithVariables {
        self.to_rwm().prove(prover)
    }
}

#[derive(Copy, Clone)]
pub struct ByUnaryRule<'a>(pub &'a ProofWithVariables);
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
pub struct BySubstitutingWith<'a>(pub &'a [ProofWithVariables]);
#[derive(Copy, Clone)]
pub struct ByScriptNamed<'a>(pub &'a str);
#[derive(Copy, Clone)]
pub struct ByConvertingBothSides<'a, B>(pub &'a ProofWithVariables, B);

impl FormulaProver for ByAxiomSchema {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
        for a in ALL_AXIOM_SCHEMAS.iter() {
            if let Ok(s) = a.inference().conclusion.substitutions_to_become(&formula) {
                return Ok(ProofWithVariables::new(a.specialize(s), Vec::new()).unwrap());
            }
        }
        Err(format!("No axiom schema matched {formula}"))
    }
}

impl FormulaProver for BySpecializingAxiom {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
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
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
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
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
        // TODO: be more efficient I guess?
        // TODO fix duplicate code ID 39483029345
        let [a, b] = formula
            .as_eq_sides()
            .unwrap()
            .map(|s| s.unfold_up_to_n_subformulas_proof(100));
        ProofWithVariables::eq_trans_chain(&[a, b.flip_conclusion()])
    }
}

impl FormulaProver for ByGeneralizedUnfolding {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
        // TODO: be more efficient I guess?
        // TODO fix duplicate code ID 39483029345
        let [a, b] = formula
            .as_eq_sides()
            .unwrap()
            .map(|s| s.generalized_unfold_up_to_n_subformulas_proof(100));
        ProofWithVariables::eq_trans_chain(&[a, b.flip_conclusion()])
    }
}

impl<B: FormulaProver> FormulaProver for ByConvertingBothSides<B> {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
        let ByConvertingBothSides(premise, how) = self;
        let [a, b] = premise.conclusion().as_eq_sides().unwrap();
        let [c, d] = formula.as_eq_sides().unwrap();
        let l = how.try_prove(ic!(a = c).to_rwm())?;
        let r = how.try_prove(ic!(b = d).to_rwm())?;
        Ok(ProofWithVariables::eq_trans_chain(&[l.flip_conclusion(), premise.clone(), r]).unwrap())
    }
}

impl FormulaProver for BySubstitutingWith<'_> {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
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
                ProofWithVariables::new(
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
                ProofWithVariables::new(
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
                Ok(ProofWithVariables::eq_trans_chain(&[fp, xp]).unwrap())
            }
        }
    }
}

impl FormulaProver for ByScriptNamed<'_> {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
        todo(formula)
    }
}
