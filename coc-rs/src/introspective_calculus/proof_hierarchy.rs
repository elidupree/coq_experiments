use crate::introspective_calculus::inference::Inference;
use crate::introspective_calculus::raw_proofs::{CleanExternalRuleInstance, ExternalRuleInstance};
use crate::introspective_calculus::{RWMFormula, RawFormula};
use std::cmp::max;
use std::collections::BTreeSet;
use std::iter::zip;
use std::ops::Deref;
use std::sync::Arc;

// later to be extended to ordinals
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct PremiseLevel(PremiseLevelInner);

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq)]
enum PremiseLevelInner {
    NoPremiseUsed,
    Finite(u32),
}

pub struct FullySpecifiedInference {
    pub inference: Inference,
    pub argument_order: Vec<String>,
    pub level: Level,
}

#[derive(Clone)]
pub struct Proof(Arc<ProofInner>);

pub struct ProofInner {
    what_was_proved: WhatWasProved,
    derivation: ProofDerivation,
}

pub enum ProofDerivation {
    Premise(usize),
    Rule(ProofByRule),
    EqualConclusion(ProofByEqualConclusion),
}

pub struct WhatWasProved {
    pub premises: BTreeSet<RWMFormula>,
    pub level: PremiseLevel,
    pub conclusion: RWMFormula,
}

pub struct ProofByRule {
    pub rule_instance: CleanExternalRuleInstance,
    pub premises: Vec<Proof>,
}
pub struct ProofByEqualConclusion {
    pub source_proof: Proof,
    pub equivalence: Proof,
}

impl Deref for Proof {
    type Target = ProofInner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl From<ProofInner> for Proof {
    fn from(value: ProofInner) -> Self {
        Proof(Arc::new(value))
    }
}

impl PremiseLevel {
    pub fn no_premise_used() -> Self {
        PremiseLevel(PremiseLevelInner::NoPremiseUsed)
    }
    pub fn premise() -> Self {
        PremiseLevel(PremiseLevelInner::Finite(0))
    }
    pub fn successor(&self) -> Self {
        match self.0 {
            PremiseLevelInner::NoPremiseUsed => PremiseLevel(PremiseLevelInner::NoPremiseUsed),
            PremiseLevelInner::Finite(l) => PremiseLevel(PremiseLevelInner::Finite(l + 1)),
        }
    }
}

impl FullySpecifiedInference {
    pub fn internal_form(&self) -> RawFormula {}
}

impl Proof {
    pub fn by_premise(premises: Vec<RWMFormula>, which: usize) -> Proof {
        assert!(premises.get(which).is_some());
        ProofInner {
            premises,
            derivation: ProofDerivation::Premise(which),
        }
        .into()
    }
    pub fn by_rule(
        premises: Vec<RWMFormula>,
        rule_premise_providers: Vec<Proof>,
        rule_instance: CleanExternalRuleInstance,
    ) -> Proof {
        let required: Vec<RWMFormula> = rule_instance.premises().collect();
        assert_eq!(
            rule_premise_providers.len(),
            required.len(),
            "wrong number of premises"
        );
        for (provider, required) in zip(&rule_premise_providers, required) {
            assert_eq!(
                provider.premises, premises,
                "premises don't match in by_rule"
            );
            assert_eq!(
                provider.conclusion(),
                required,
                "conclusion doesn't match premise in by_rule"
            );
        }
        ProofInner {
            premises,
            derivation: ProofDerivation::Rule(ProofByRule {
                rule_instance,
                premises: rule_premise_providers,
            }),
        }
        .into()
    }
    pub fn by_equal_conclusion(source_proof: Proof, equivalence: Proof) -> Proof {
        assert_eq!(
            source_proof.conclusion(),
            equivalence.conclusion().as_eq_sides().unwrap()[0],
            "proofs don't match in by_equal_conclusion"
        );
        assert_eq!(
            source_proof.premises, equivalence.premises,
            "premises don't match in by_equal_conclusion"
        );

        ProofInner {
            premises: source_proof.premises.clone(),
            derivation: ProofDerivation::EqualConclusion(ProofByEqualConclusion {
                source_proof,
                equivalence,
            }),
        }
        .into()
    }

    pub fn premise_level(&self) -> PremiseLevel {
        match &self.derivation {
            ProofDerivation::Premise(_) => PremiseLevel::premise(),
            ProofDerivation::Rule(proof) => proof
                .premises
                .iter()
                .map(Proof::premise_level)
                .max()
                .unwrap_or(PremiseLevel::no_premise_used()),
            ProofDerivation::EqualConclusion(proof) => max(
                proof.source_proof.premise_level(),
                proof.equivalence.premise_level().successor(),
            ),
        }
    }

    pub fn conclusion(&self) -> RWMFormula {
        match &self.derivation {
            ProofDerivation::Premise(which) => self.premises[which].clone(),
            ProofDerivation::Rule(proof) => proof.rule_instance.conclusion(),
            ProofDerivation::EqualConclusion(proof) => {
                proof.equivalence.conclusion().as_eq_sides().unwrap()[1].clone()
            }
        }
    }
}
