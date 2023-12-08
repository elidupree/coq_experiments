use crate::introspective_calculus::inference::Inference;
use crate::introspective_calculus::proof_hierarchy::ProofWithVariables;
use crate::introspective_calculus::raw_proofs::{RuleTrait, ALL_AXIOMS};
use crate::introspective_calculus::raw_proofs_ext::ALL_AXIOM_SCHEMAS;
use crate::introspective_calculus::{Formula, RWMFormula, RawFormula};
use crate::utils::todo;

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

pub struct ByAxiomSchema;
pub struct BySpecializingAxiom;
pub struct ByPartiallySpecializingAxiom;
pub struct ByUnfolding;
pub struct BySubstitutingWith<'a>(pub &'a [ProofWithVariables]);
pub struct ByScriptNamed<'a>(pub &'a str);

impl FormulaProver for ByAxiomSchema {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
        for a in ALL_AXIOM_SCHEMAS.iter() {
            if let Ok(s) = a.inference().conclusion.substitutions_to_become(&formula) {
                return Ok(ProofWithVariables::new(a.specialize(s), Vec::new()).unwrap());
            }
        }
        Err("No axiom schema matched".to_string())
    }
}

impl FormulaProver for BySpecializingAxiom {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
        let Some(formula) = formula.to_raw() else {
            return Err("Can't specialize axiom to non-raw formula".to_string());
        };
        for axiom in ALL_AXIOMS.values() {
            if let Ok(args) = axiom.internal_form.args_to_return(&formula) {
                return Ok(axiom.proof().specialize(&args));
            }
        }
        Err("No axiom matched".to_string())
    }
}

impl FormulaProver for ByPartiallySpecializingAxiom {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
        let Some(formula) = formula.already_uncurried_function_equivalence() else {
            return Err("Can't specialize axiom to non-raw formula".to_string());
        };
        for axiom in ALL_AXIOMS.values() {
            if let Ok(args) = axiom.internal_form.generalized_args_to_return(&formula) {
                return Ok(axiom.proof().partially_specialize(&args).proof().clone());
            }
        }
        Err("No axiom matched".to_string())
    }
}

impl FormulaProver for ByUnfolding {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
        todo(formula)
    }
}

impl FormulaProver for BySubstitutingWith<'_> {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
        todo(formula)
    }
}

impl FormulaProver for ByScriptNamed<'_> {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
        todo(formula)
    }
}
