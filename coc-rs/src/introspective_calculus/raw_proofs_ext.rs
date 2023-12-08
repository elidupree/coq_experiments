use crate::introspective_calculus::proof_hierarchy::{ProofWithVariables, Proven};
use crate::introspective_calculus::raw_proofs::{
    Axiom, CleanExternalRule, RawProof, Rule, ALL_AXIOMS,
};
use crate::introspective_calculus::uncurried_function::UncurriedFunctionEquivalence;
use crate::introspective_calculus::{RawFormula, Substitutions};
use itertools::Itertools;
use std::sync::LazyLock;

impl Axiom {
    pub fn proof(&self) -> Proven<UncurriedFunctionEquivalence> {
        Proven::new(
            self.internal_form.clone(),
            ProofWithVariables::new(
                Rule::from(self.clone()).specialize(Substitutions::new()),
                Vec::new(),
            )
            .unwrap(),
        )
    }
}

pub static ALL_AXIOM_SCHEMAS: LazyLock<Vec<Rule>> = LazyLock::new(|| {
    ALL_AXIOMS
        .values()
        .map(|a| Rule::from(a.clone()))
        .chain([
            Rule::from(CleanExternalRule::DefinitionOfConst),
            Rule::from(CleanExternalRule::DefinitionOfFuse),
        ])
        .collect()
});

impl RawProof {
    // pub fn substitute_in_conclusion(&self, equivalence: RawProof) -> Option<RawProof> {
    //     let [a, b] = equivalence.conclusion().as_eq_sides().unwrap();
    //     if self.conclusion() == a {
    //         Some(RawProof::new())
    //     }
    // }
    pub fn with_zero_variables(&self) -> ProofWithVariables {
        ProofWithVariables::new(
            self.rule_instance.with_zero_variables(),
            self.premises
                .iter()
                .map(|c| c.with_zero_variables())
                .collect(),
        )
        .unwrap()
    }
    pub fn eq_refl(formula: RawFormula) -> RawProof {
        ProofWithVariables::eq_refl(formula.into()).to_raw()
    }
    pub fn flip_conclusion(&self) -> RawProof {
        self.with_zero_variables().flip_conclusion().to_raw()
    }

    pub fn eq_trans_chain(components: &[RawProof]) -> Result<RawProof, String> {
        Ok(ProofWithVariables::eq_trans_chain(
            &components
                .iter()
                .map(|c| c.with_zero_variables())
                .collect_vec(),
        )?
        .to_raw())
    }
}
