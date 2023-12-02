use crate::ic;
use crate::introspective_calculus::raw_proofs::{CleanExternalRuleInstance, RawProof};
use crate::introspective_calculus::{Formula, RWMFormula, RawFormula, Substitutions, ToFormula};
use crate::utils::todo;
use hash_capsule::HashCapsule;
use std::cmp::max;
use std::collections::BTreeSet;
use std::iter::zip;
use std::ops::Deref;
use std::sync::Arc;

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct WeaknessLevel {
    // later to be extended to ordinals
    // plus_omegas: usize,
    plus_ones: usize,
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct WeakProposition {
    proposition: RWMFormula,
    weakness_level: WeaknessLevel,
    formula_cache: RWMFormula,
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct Proven<T> {
    formula: T,
    proof: Proof,
}

impl<T> Proven<T> {
    pub fn new(formula: T, proof: Proof) -> Proven<T> {
        // TODO: check that the proof proves the correct formula
        Proven { formula, proof }
    }
    pub fn formula(&self) -> &T {
        &self.formula
    }
    pub fn proof(&self) -> &Proof {
        &self.proof
    }
}

impl WeakProposition {
    pub fn new(proposition: RWMFormula, weakness_level: WeaknessLevel) -> WeakProposition {
        let formula_cache = weakness_level
            .wrap_proposition(proposition.to_formula())
            .to_rwm();
        WeakProposition {
            proposition,
            weakness_level,
            formula_cache,
        }
    }

    pub fn proposition(&self) -> RWMFormula {
        self.proposition.clone()
    }

    pub fn weakness_level(&self) -> WeaknessLevel {
        self.weakness_level.clone()
    }

    pub fn formula(&self) -> RWMFormula {
        self.formula_cache.clone()
    }

    pub fn weaken_to(&self, target_level: WeaknessLevel) -> WeakProposition {
        assert!(target_level >= self.weakness_level);
        WeakProposition::new(self.proposition.clone(), target_level)
    }
    pub fn strength_predecessor(&self) -> Option<WeakProposition> {
        Some(WeakProposition::new(
            self.proposition.clone(),
            self.weakness_level.predecessor()?,
        ))
    }

    pub fn weakening_implication_proof(&self, target_level: WeaknessLevel) -> Proof {
        assert!(target_level >= self.weakness_level);
        if target_level == self.weakness_level {
            Proof::imp_refl()
        } else {
            let pred = self.weakening_implication_proof(target_level.predecessor().unwrap());
            // we have:
            // (self -> pred)
            //
            Proof::imp_trans(pred, "true_equals_intro")
        }
    }
}

impl Proven<WeakProposition> {
    pub fn weaken_to(&self, target_level: WeaknessLevel) -> Proven<WeakProposition> {
        assert!(target_level >= self.formula.weakness_level);
        if target_level == self.formula.weakness_level {
            self.clone()
        } else {
            let pred = self.weaken_to(self.formula.weakness_level.predecessor().unwrap());
            Proven::new(
                WeakProposition(self.formula.proposition.clone(), target_level),
                Proof::("true_equals_intro", pred.proof)
            )
        }
    }
}

pub struct InternalizedInference {
    // yes Some<[]> is different from None
    premises: Option<Vec<RWMFormula>>,
    conclusion: WeakProposition,
    argument_order: Vec<String>,
    formula_cache: RawFormula,
}

impl InternalizedInference {
    pub fn premises(&self) -> &Option<Vec<RWMFormula>> {
        &self.premises
    }
    pub fn conclusion(&self) -> &WeakProposition {
        &self.conclusion
    }
    pub fn argument_order(&self) -> &Vec<String> {
        &self.argument_order
    }
    pub fn formula(&self) -> &RawFormula {
        &self.formula_cache
    }

    pub fn new(
        premises: Option<Vec<RWMFormula>>,
        conclusion: WeakProposition,
        argument_order: Vec<String>,
    ) -> InternalizedInference {
        let formula_cache;
        // TODO: uncurried instead of curried
        let to_fn = |f: &Formula| f.metavariables_to_arguments(&self.argument_order);
        if let Some(premises) = &self.premises {
            let internal_premises =
                Formula::true_and_and(&premises.iter().map(|f| f.to_formula()).collect::<Vec<_>>())
                    .unwrap();
            let p: Formula = to_fn(&internal_premises);
            let pc: Formula = to_fn(&Formula::and([internal_premises, conclusion]).unwrap());
            formula_cache = ic!(p = pc).already_raw().unwrap()
        } else {
            let [c1, c2] = conclusion.as_eq_sides().unwrap().each_ref().map(to_fn);
            formula_cache = ic!(c1 = c2).already_raw().unwrap()
        }
        InternalizedInference {
            premises,
            conclusion,
            argument_order,
            formula_cache,
        }
    }
    pub fn forget_disambiguation(&self) -> WhatWasProved {
        WhatWasProved {
            premises: self.premises.iter().flatten().cloned().collect(),
            conclusion: self.conclusion.clone(),
        }
    }
}

impl Proven<InternalizedInference> {
    pub fn weaken_to(&self, target_level: WeaknessLevel) -> Proven<InternalizedInference> {
        // get the "strong-implication of weakening" for the interior,
        let internal = self.formula
            .conclusion
            .weakening_implication_proof(target_level);
        // then use "strong-implication under hypotheticals"
        Proof::imp_trans(self.proof, internal)
    }
}

#[derive(Clone)]
pub struct Proof(Arc<ProofInner>);

pub struct ProofInner {
    derivation: ProofDerivation,
    what_was_proved_cache: WhatWasProved,
}

pub enum ProofDerivation {
    Premise(RWMFormula),
    CleanRule(ProofByCleanRule),
    StrengthenSuccessor(Proof),
}

pub struct WhatWasProved {
    pub premises: BTreeSet<RWMFormula>,
    pub conclusion: WeakProposition,
}

pub struct ProofByCleanRule {
    pub rule_instance: CleanExternalRuleInstance,
    pub premises: Vec<Proof>,
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
        WeaknessLevel { plus_ones: 0 }
    }
    pub fn premise() -> Self {
        WeaknessLevel { plus_ones: 0 }
    }
    pub fn successor(&self) -> Self {
        WeaknessLevel {
            plus_ones: self.plus_ones + 1,
        }
    }
    pub fn predecessor(&self) -> Option<Self> {
        Some(WeaknessLevel {
            plus_ones: self.plus_ones.saturating_sub(1)?,
        })
    }
    // pub fn successors_of_members(&self) -> Self {
    //     match *(self.0) {
    //         WeaknessLevelInner::Successor(_) => self.successor(),
    //         _ => self.clone(),
    //     }
    // }

    pub fn wrap_proposition(&self, proposition: Formula) -> Formula {
        match self.predecessor() {
            None => proposition,
            Some(n) => {
                ic!(True = { n.wrap_proposition(proposition) })
            }
        }
    }

    // return (weak(A) and weak(B)) = weak(A and B)
    pub fn distribute_and(&self, a: RawFormula, b: RawFormula) -> Proof {
        match self.predecessor() {
            None => {
                Proof::eq_refl()
            }
            Some(pred) => {
                let last = Formula::and(WeakProposition(a), WeakProposition(b)).prove("distribute_and");
                let pred = pred.distribute_and(a, b);
                Proof::eq_trans(last, pred)
            }
        }
    }
}

impl WhatWasProved {
    pub fn proves(&self, inference: &InternalizedInference) -> bool {
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
                conclusion: WeakProposition::new(premise, WeaknessLevel::premise()),
            },
        }
        .into()
    }
    pub fn by_clean_rule(
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
            conclusion: WeakProposition::new(
                rule_instance.conclusion(),
                rule_premise_providers
                    .iter()
                    .map(|p| p.weakness_level)
                    .max()
                    .unwrap_or(WeaknessLevel::no_premise_used()),
            ),
        };
        ProofInner {
            derivation: ProofDerivation::CleanRule(ProofByCleanRule {
                rule_instance,
                premises: rule_premise_providers,
            }),
            what_was_proved_cache,
        }
        .into()
    }
    pub fn by_strengthen_successor(weak_proof: Proof) -> Proof {
        assert_eq!(
            weak_proof.conclusion.as_eq_sides().unwrap()[0],
            Formula::prop_true().to_rwm(),
            "proof doesn't fit by_strengthen_successor"
        );

        let what_was_proved_cache = WhatWasProved {
            premises: weak_proof.premises.clone(),
            conclusion: WeakProposition::new(
                weak_proof.conclusion.as_eq_sides().unwrap()[1].clone(),
                if weak_proof.premises.is_empty() {
                    WeaknessLevel::no_premise_used()
                } else {
                    weak_proof.weakness_level.successor()
                },
            ),
        };
        ProofInner {
            derivation: ProofDerivation::StrengthenSuccessor(weak_proof),
            what_was_proved_cache,
        }
        .into()
    }

    pub fn what_was_proved(&self) -> &WhatWasProved {
        &self.what_was_proved_cache
    }

    pub fn to_raw(&self) -> RawProof {
        assert!(
            self.premises.is_empty() && self.conclusion.formula().is_raw(),
            "can only use Proof::to_raw() when there's no arguments or premises"
        );
        self.use_externally(&Substitutions::new(), &[]).unwrap()
    }

    pub fn use_externally(
        &self,
        arguments: &Substitutions,
        premise_proofs: &[RawProof],
    ) -> Result<RawProof, String> {
        match &self.derivation {
            ProofDerivation::Premise(p) => {
                let specialized_premise = p.with_metavariables_replaced_rwm(arguments);
                premise_proofs
                    .iter()
                    .find(|premise_proof| premise_proof.conclusion() == specialized_premise)
                    .cloned()
                    .ok_or_else(|| {
                        format!("No proof of premise {} was provided", specialized_premise)
                    })
            }
            ProofDerivation::CleanRule(proof) => {
                let instance = proof
                    .rule_instance
                    .further_specialize(arguments)
                    .assume_raw();
                RawProof::new(
                    instance,
                    proof
                        .premises
                        .iter()
                        .map(|p| p.use_externally(arguments, premise_proofs))
                        .collect(),
                )
            }
            ProofDerivation::StrengthenSuccessor(weak_proof) => {
                let raw_weak_proof = weak_proof.use_externally(arguments, premise_proofs)?;
                if weak_proof.premises.is_empty() {
                    RawProof::new(
                        STRENGTHEN_SUCCESSOR.specialize().assume_raw(),
                        vec![raw_weak_proof],
                    )
                } else {
                    raw_weak_proof
                }
            }
        }
    }
    pub fn internalize(&self, inference: &InternalizedInference) -> Proven<InternalizedInference> {
        assert!(self.what_was_proved().proves(inference));
        let result: Proven<InternalizedInference> = match &self.derivation {
            ProofDerivation::Premise(p) => todo(()),
            ProofDerivation::CleanRule(proof) => proof.internalize(inference),
            ProofDerivation::StrengthenSuccessor(weak_proof) => {
                if inference.premises.is_none() {
                    // with no premises, we can do raw stuff directly
                    let weak_result = weak_proof.internalize(&InternalizedInference::new(
                        None,
                        weak_proof.conclusion.unwrap(),
                        inference.argument_order.clone(),
                    ));
                    weak_result.strengthen_successor()
                } else {
                    // "strong True=C" is the same as "weak C", so just ask for it
                    weak_proof.internalize(&InternalizedInference::new(
                        inference.premises.clone(),
                        weak_proof.conclusion.strength_predecessor().unwrap(),
                        inference.argument_order.clone(),
                    ))
                }
            }
        };
        let result = result.weaken_to(inference.we);
        assert_eq!(result.conclusion(), inference.internal_form());
        result
    }
}

impl ProofByCleanRule {
    pub fn internalize(&self, inference: &InternalizedInference) -> Proven<InternalizedInference> {
        let internal_premise_providers = self.premises.iter().map(|p| {
            p.internalize(&InternalizedInference::new(
                inference.premises.clone(),
                p.conclusion
                    .weaken_to(inference.conclusion.weakness_level.clone()),
                inference.argument_order.clone(),
            ))
        });
        // we now have, e.g.:
        // (P=Q) -> (True = (A=B))   (i.e. (x=>(P=Q)) = (x=>(P, True)=(Q, (A=B))))
        // (P=Q) -> (True = (C=D))    "
        // and the rule,
        // (A=B), (C=D) |- (E=F)
        // which internalizes to
        // (x => ((*, x[0]), x[2]) = ((*, x[1]), x[3]))
        // = (x => (((*, x[0]), x[2]), x[4]) = (((*, x[1]), x[3]), x[4]))
        // basic idea is:
        // spawn all premises, to get P = P and ((weak A) and (weak C))
        // apply weak-and distribution, get P = P and weak (A and C)
        // partially specialize the rule to get (A and C) = (A and C) and E
        // substitute
        // then despawn all premises
        self.rule_instance.weaken(inference.weakness_level)
    }
}
