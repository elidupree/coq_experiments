use crate::introspective_calculus::inference::Inference;
use crate::introspective_calculus::proof_hierarchy::{ProofWithPremises, ProofWithVariables};
use crate::introspective_calculus::{Formula, RWMFormula, RawFormula};
use crate::utils::todo;

pub trait FormulaProver {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String>;
}
pub trait InferenceProver {
    fn try_prove(&self, inference: Inference) -> Result<ProofWithPremises, String>;
}

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

pub struct ByRule;
pub struct BySpecializingAxiom;
pub struct ByPartiallySpecializingAxiom;
pub struct ByUnfolding;
pub struct BySubstitutingWith<'a>(pub &'a [ProofWithVariables]);
pub struct ByScriptNamed<'a>(pub &'a str);

impl FormulaProver for ByRule {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
        todo(formula)
    }
}

impl FormulaProver for BySpecializingAxiom {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
        todo(formula)
    }
}

impl FormulaProver for ByPartiallySpecializingAxiom {
    fn try_prove(&self, formula: RWMFormula) -> Result<ProofWithVariables, String> {
        todo(formula)
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
