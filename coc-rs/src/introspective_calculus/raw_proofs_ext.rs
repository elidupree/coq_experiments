use crate::introspective_calculus::proof_hierarchy::{Proof, Proven};
use crate::introspective_calculus::provers::ByAssumingIt;
use crate::introspective_calculus::raw_proofs::{
    Axiom, CleanExternalRule, RawProof, Rule, RuleTrait, ALL_AXIOMS,
};
use crate::introspective_calculus::uncurried_function::UncurriedFunctionEquivalence;
use crate::introspective_calculus::{RawFormula, Substitutions, ToFormula};
use itertools::Itertools;
use std::sync::LazyLock;

impl Axiom {
    pub fn proof(&self) -> Proven<UncurriedFunctionEquivalence> {
        Proven::new(
            self.internal_form.clone(),
            Proof::by_rule(
                Rule::from(self.clone()).specialize(Substitutions::new()),
                Vec::new(),
            )
            .unwrap(),
        )
    }
}

impl Rule {
    pub fn to_proof(&self) -> Proof {
        Proof::by_rule(
            self.specialize(
                self.inference()
                    .free_metavariables()
                    .iter()
                    .map(|name| (name.clone(), name.to_formula().to_rwm()))
                    .collect(),
            ),
            self.inference()
                .premises
                .iter()
                .map(|premise| premise.prove(ByAssumingIt))
                .collect(),
        )
        .unwrap()
    }
}

pub static ALL_AXIOM_SCHEMAS: LazyLock<Vec<Rule>> = LazyLock::new(|| {
    ALL_AXIOMS
        .iter()
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
    pub fn to_fancy_proof(&self) -> Proof {
        Proof::by_rule(
            self.rule_instance.with_zero_variables(),
            self.premises.iter().map(|c| c.to_fancy_proof()).collect(),
        )
        .unwrap()
    }
    pub fn eq_refl(formula: RawFormula) -> RawProof {
        Proof::eq_refl(formula.into()).to_raw()
    }
    pub fn flip_conclusion(&self) -> RawProof {
        self.to_fancy_proof().flip_conclusion().to_raw()
    }

    pub fn eq_trans_chain(components: &[RawProof]) -> Result<RawProof, String> {
        Ok(
            Proof::eq_trans_chain(&components.iter().map(|c| c.to_fancy_proof()).collect_vec())?
                .to_raw(),
        )
    }
}
