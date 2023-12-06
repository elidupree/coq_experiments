use crate::introspective_calculus::proof_hierarchy::ProofWithVariables;
use crate::introspective_calculus::raw_proofs::RawProof;
use crate::introspective_calculus::RawFormula;
use itertools::Itertools;

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
