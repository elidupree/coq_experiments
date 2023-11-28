use crate::ic;
use crate::introspective_calculus::raw_proofs::{CleanExternalRuleInstance, RawProof};
use crate::introspective_calculus::{Formula, RWMFormula, RawFormula, ToFormula};
use crate::utils::todo;
use hash_capsule::HashCapsule;
use std::cmp::max;
use std::collections::BTreeSet;
use std::iter::zip;
use std::ops::Deref;
use std::sync::Arc;

// later to be extended to ordinals
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct WeaknessLevel(HashCapsule<WeaknessLevelInner>);

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
enum WeaknessLevelInner {
    Zero,
    Successor(WeaknessLevel),
}

pub struct FullySpecifiedInference {
    // yes Some<[]> is different from None
    pub premises: Option<Vec<RWMFormula>>,
    pub conclusion: RWMFormula,
    pub argument_order: Vec<String>,
    pub weakness_level: WeaknessLevel,
}

#[derive(Clone)]
pub struct Proof(Arc<ProofInner>);

pub struct ProofInner {
    derivation: ProofDerivation,
    what_was_proved_cache: WhatWasProved,
}

pub enum ProofDerivation {
    Premise(RWMFormula),
    Rule(ProofByRule),
    EqualConclusion(ProofByEqualConclusion),
}

pub struct WhatWasProved {
    pub premises: BTreeSet<RWMFormula>,
    pub weakness_level: WeaknessLevel,
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
impl Deref for ProofInner {
    type Target = WhatWasProved;

    fn deref(&self) -> &Self::Target {
        &self.what_was_proved_cache
    }
}

impl WeaknessLevel {
    pub fn no_premise_used() -> Self {
        WeaknessLevel(HashCapsule::new(WeaknessLevelInner::Zero))
    }
    pub fn premise() -> Self {
        Self::no_premise_used() //.successor()
    }
    pub fn successor(&self) -> Self {
        WeaknessLevel(HashCapsule::new(WeaknessLevelInner::Successor(
            self.clone(),
        )))
    }
    pub fn successors_of_members(&self) -> Self {
        match *(self.0) {
            WeaknessLevelInner::Successor(_) => self.successor(),
            _ => self.clone(),
        }
    }

    pub fn wrap_proposition(&self, proposition: Formula) -> Formula {
        match *(self.0) {
            WeaknessLevelInner::Zero => proposition,
            WeaknessLevelInner::Successor(n) => {
                ic!(True = { n.wrap_proposition(proposition) })
            }
        }
    }
}

impl FullySpecifiedInference {
    pub fn internal_form(&self) -> RawFormula {
        let curry = |f: &Formula| f.metavariables_to_arguments(&self.argument_order);
        let conclusion = self
            .weakness_level
            .wrap_proposition(self.conclusion.to_formula());
        if let Some(premises) = &self.premises {
            let internal_premises =
                Formula::true_and_and(&premises.iter().map(|f| f.to_formula()).collect::<Vec<_>>())
                    .unwrap();
            let p: Formula = curry(&internal_premises);
            let pc: Formula = curry(&Formula::and([internal_premises, conclusion]).unwrap());
            ic!(p = pc).already_raw().unwrap()
        } else {
            let [c1, c2] = conclusion.as_eq_sides().unwrap().each_ref().map(curry);
            ic!(c1 = c2).already_raw().unwrap()
        }
    }
}
impl WhatWasProved {
    pub fn proves(&self, inference: &FullySpecifiedInference) -> bool {
        // can prove something weaker or with more premises
        self.premises.iter().all(|provided| {
            inference
                .premises
                .iter()
                .flatten()
                .any(|required| required == provided)
        }) && inference.conclusion == self.conclusion
            && inference.weakness_level >= self.weakness_level
    }
}

impl Proof {
    pub fn by_premise(premise: RWMFormula) -> Proof {
        ProofInner {
            derivation: ProofDerivation::Premise(premise.clone()),
            what_was_proved_cache: WhatWasProved {
                premises: [premise.clone()].into_iter().collect(),
                weakness_level: WeaknessLevel::premise(),
                conclusion: premise,
            },
        }
        .into()
    }
    pub fn by_rule(
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
                provider.conclusion, required,
                "conclusion doesn't match premise in by_rule"
            );
        }
        let what_was_proved_cache = WhatWasProved {
            premises: rule_premise_providers
                .iter()
                .flat_map(|provider| provider.premises.iter().cloned())
                .collect(),
            weakness_level: rule_premise_providers
                .iter()
                .map(|p| p.weakness_level)
                .max()
                .unwrap_or(WeaknessLevel::no_premise_used()),
            conclusion: rule_instance.conclusion(),
        };
        ProofInner {
            derivation: ProofDerivation::Rule(ProofByRule {
                rule_instance,
                premises: rule_premise_providers,
            }),
            what_was_proved_cache,
        }
        .into()
    }
    pub fn by_equal_conclusion(source_proof: Proof, equivalence: Proof) -> Proof {
        assert_eq!(
            source_proof.conclusion,
            equivalence.conclusion.as_eq_sides().unwrap()[0],
            "proofs don't match in by_equal_conclusion"
        );
        assert_eq!(
            source_proof.premises, equivalence.premises,
            "premises don't match in by_equal_conclusion"
        );

        let what_was_proved_cache = WhatWasProved {
            premises: [&source_proof, &equivalence]
                .into_iter()
                .flat_map(|provider| provider.premises.iter().cloned())
                .collect(),
            weakness_level: max(
                source_proof.weakness_level.clone(),
                if equivalence.premises.is_empty() {
                    WeaknessLevel::no_premise_used()
                } else {
                    equivalence.weakness_level.successor()
                },
            ),
            conclusion: equivalence.conclusion.as_eq_sides().unwrap()[1].clone(),
        };
        ProofInner {
            derivation: ProofDerivation::EqualConclusion(ProofByEqualConclusion {
                source_proof,
                equivalence,
            }),
            what_was_proved_cache,
        }
        .into()
    }

    pub fn what_was_proved(&self) -> &WhatWasProved {
        &self.what_was_proved_cache
    }

    pub fn internalize(&self, inference: &FullySpecifiedInference) -> RawProof {
        assert!(self.what_was_proved().proves(inference));
        let result: RawProof = match self.derivation {
            ProofDerivation::Premise(p) => {}
            ProofDerivation::Rule(proof) => proof.internalize(inference),
            ProofDerivation::EqualConclusion(proof) => proof.internalize(inference),
        };
        if inference.weakness_level > todo(()) {
            result = result.weaken(inference.weakness_level - todo(()));
        }
        assert_eq!(result.conclusion(), inference.internal_form());
        result
    }
}

impl ProofByRule {
    pub fn internalize(&self, inference: &FullySpecifiedInference) -> RawProof {
        let internal_premise_providers = self.premises.iter().map(|p| {
            p.internalize(&FullySpecifiedInference {
                premises: inference.premises.clone(),
                conclusion: p.conclusion.clone(),
                argument_order: inference.argument_order.clone(),
                weakness_level: inference.weakness_level.clone(),
            })
        });
        self.rule_instance.weaken(inference.weakness_level)
    }
}

impl ProofByEqualConclusion {
    pub fn internalize(&self, inference: &FullySpecifiedInference) -> RawProof {
        let internal_source_proof = self.source_proof.internalize(&FullySpecifiedInference {
            premises: inference.premises.clone(),
            conclusion: self.source_proof.conclusion.clone(),
            argument_order: inference.argument_order.clone(),
            weakness_level: inference.weakness_level.clone(),
        });
        if self.equivalence.premises.is_empty() {
            let internal_equivalence = self.equivalence.internalize(&FullySpecifiedInference {
                premises: None,
                conclusion: self.equivalence.conclusion.clone(),
                argument_order: inference.argument_order.clone(),
                weakness_level: WeaknessLevel::no_premise_used(),
            });
            internal_source_proof.substitute_in_conclusion(internal_equivalence)
        } else {
            let internal_equivalence = self.equivalence.internalize(&FullySpecifiedInference {
                premises: inference.premises.clone(),
                conclusion: self.equivalence.conclusion.clone(),
                argument_order: inference.argument_order.clone(),
                weakness_level: inference.weakness_level.predecessor(),
            });
            // now we have e.g.
            // P -> True = (True = (True = C))
            // P -> True = (True = (C = D))
            // so proceed by "transitivity under premises"

            todo(internal_equivalence)
        }
    }
}
