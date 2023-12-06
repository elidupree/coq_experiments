use crate::introspective_calculus::raw_proofs::{
    CleanExternalRule, CleanRule, RawProof, Rule, RuleInstance, StrengtheningRule,
};
use crate::introspective_calculus::uncurried_function::UncurriedFunctionEquivalence;
use crate::introspective_calculus::{Formula, RWMFormula, RawFormula, Substitutions, ToFormula};
use crate::utils::todo;
use crate::{formula, ic, inf, substitutions};
use std::collections::BTreeSet;
use std::iter::zip;
use std::ops::Deref;
use std::sync::Arc;

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct ProofWithVariables(Arc<ProofWithVariablesInner>);

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct ProofWithVariablesInner {
    pub rule_instance: RuleInstance,
    pub premises: Vec<ProofWithVariables>,
}

impl Deref for ProofWithVariables {
    type Target = ProofWithVariablesInner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct Proven<T> {
    formula: T,
    proof: ProofWithVariables,
}

impl<T> Deref for Proven<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.formula
    }
}

impl<T> Proven<T> {
    pub fn new(formula: T, proof: ProofWithVariables) -> Proven<T> {
        // TODO: check that the proof proves the correct formula
        Proven { formula, proof }
    }
    pub fn formula(&self) -> &T {
        &self.formula
    }
    pub fn proof(&self) -> &ProofWithVariables {
        &self.proof
    }
}

impl ProofWithVariables {
    pub fn new(
        rule_instance: RuleInstance,
        premises: Vec<ProofWithVariables>,
    ) -> Result<ProofWithVariables, String> {
        let required_premises: Vec<RWMFormula> = rule_instance.premises().collect();
        if premises.len() != required_premises.len() {
            return Err(format!(
                "Wrong number of premises to rule `{}` (need {}, got {})",
                rule_instance.rule,
                required_premises.len(),
                premises.len(),
            ));
        }
        for (required, provided) in zip(&required_premises, &premises) {
            if provided.conclusion() != *required {
                return Err(format!(
                    "Incorrect premise provided to rule {} (need {required}, got {})",
                    rule_instance.rule,
                    provided.conclusion(),
                ));
            }
        }
        Ok(ProofWithVariables(Arc::new(ProofWithVariablesInner {
            rule_instance,
            premises,
        })))
    }

    pub fn conclusion(&self) -> RWMFormula {
        self.rule_instance.conclusion()
    }

    pub fn to_raw(&self) -> RawProof {
        assert!(
            self.conclusion().is_raw(),
            "can only use ProofWithVariables::to_raw() when there's no variables"
        );
        self.use_externally(&Substitutions::new()).unwrap()
    }

    pub fn use_externally(&self, arguments: &Substitutions) -> Result<RawProof, String> {
        RawProof::new(
            self.rule_instance
                .further_specialize(arguments)
                .assume_raw(),
            self.premises
                .iter()
                .map(|p| p.use_externally(arguments))
                .collect::<Result<_, _>>()?,
        )
    }
    pub fn internal_conclusion(&self, argument_order: &[String]) -> UncurriedFunctionEquivalence {
        UncurriedFunctionEquivalence {
            sides: self
                .conclusion()
                .as_eq_sides()
                .unwrap()
                .map(|s| s.to_uncurried_function_of(argument_order)),
        }
    }
    pub fn internalize(&self, argument_order: &[String]) -> RawProof {
        let conclusion = self.internal_conclusion(argument_order);
        let premise_proofs: Vec<RawProof> = self
            .premises
            .iter()
            .map(|p| p.internalize(argument_order))
            .collect();
        let result = match &self.rule_instance.rule {
            Rule::Clean(CleanRule::External(c)) => match c {
                CleanExternalRule::EqSym => premise_proofs[0].flip_conclusion(),
                CleanExternalRule::EqTrans => RawProof::eq_trans_chain(&premise_proofs),
                CleanExternalRule::DefinitionOfConst | CleanExternalRule::DefinitionOfFuse => {
                    conclusion.prove_by_partially_specializing_axiom()
                }
                CleanExternalRule::SubstituteInLhs | CleanExternalRule::SubstituteInRhs => {
                    conclusion
                        .formula()
                        .prove_by_substituting_with(&premise_proofs)
                }
            },
            Rule::Clean(CleanRule::Axiom(axiom)) => {
                // The axiom guarantees a=b, and
                // since these are raw formulas, only one value of `conclusion` is possible: const a = const b
                //assert_eq!(todo(()),todo(()));
                conclusion
                    .formula()
                    .prove_by_substituting_with(&[axiom.proof()])
            }
            Rule::Strengthening(s) => match s {
                StrengtheningRule::StrengthenSuccessor => {
                    // StrengthenSuccessor is
                    // `const True = fuse (const equals) A B |- A = B`
                    // so premise_proofs[0] proves
                    // const True = fuse (const equals) A B
                    // or, raw-ly,
                    // const (const True) = (l => m => (Alm = Blm))
                    // and the conclusion we need is
                    // l => Al = Bl
                    conclusion
                        .formula()
                        .prove_by_script_named("generalize_strengthen_successor")
                }
            },
        };
        assert_eq!(result.conclusion(), conclusion.formula());
        result
    }

    pub fn eq_refl(a: RWMFormula) -> ProofWithVariables {
        ic!(a = a).prove_by_script_named("eq_refl").unwrap()
    }

    pub fn flip_conclusion(&self) -> ProofWithVariables {
        let [a, b] = self.conclusion().as_eq_sides().unwrap();
        ProofWithVariables::new(
            Rule::from(CleanExternalRule::EqSym).specialize(substitutions! {A:a,B:b}),
            vec![self.clone()],
        )
        .unwrap()
    }

    pub fn eq_trans_chain(components: &[ProofWithVariables]) -> Result<ProofWithVariables, String> {
        let (first, rest) = components
            .split_first()
            .ok_or_else(|| "eq_trans_chain must have at least 1 element".to_string())?;
        let mut result = first.clone();
        for inference in rest {
            let [a, b1] = result.conclusion().as_eq_sides().unwrap();
            let [b2, c] = inference.conclusion().as_eq_sides().unwrap();

            if b1 != b2 {
                return Err(format!(
                    "eq_trans_chain components have mismatched conclusions: `{}` vs `{}`",
                    result.conclusion(),
                    inference.conclusion()
                ));
            }
            result = ProofWithVariables::new(
                Rule::from(CleanExternalRule::EqTrans)
                    .specialize(substitutions! {A: a, B: b1, C: c}),
                vec![result, inference.clone()],
            )
            .unwrap()
        }
        Ok(result)
    }
}

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

    pub fn weakening_implication_proof(&self, target_level: WeaknessLevel) -> ProofWithPremises {
        assert!(target_level >= self.weakness_level);
        if target_level == self.weakness_level {
            ProofWithPremises::imp_refl()
        } else {
            let pred = self.weakening_implication_proof(target_level.predecessor().unwrap());
            // we have:
            // (self -> pred)
            //
            ProofWithPremises::imp_trans(pred, "true_equals_intro")
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
                WeakProposition::new(self.formula.proposition.clone(), target_level),
                ProofWithPremises::uhh("true_equals_intro", pred.proof),
            )
        }
    }
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct InternalizedInference {
    premises: Vec<RWMFormula>,
    conclusion: WeakProposition,
    argument_order: Vec<String>,
    formula_cache: RawFormula,
}

impl InternalizedInference {
    pub fn premises(&self) -> &Vec<RWMFormula> {
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
        premises: Vec<RWMFormula>,
        conclusion: WeakProposition,
        argument_order: Vec<String>,
    ) -> InternalizedInference {
        // TODO: uncurried instead of curried
        let to_fn = |f: &Formula| f.to_rwm().to_uncurried_function_of(&argument_order);
        let internal_premises =
            Formula::and_and_true(&premises.iter().map(|f| f.to_formula()).collect::<Vec<_>>())
                .unwrap();
        let p = to_fn(&internal_premises).formula();
        let pc = to_fn(&Formula::and([internal_premises, conclusion]).unwrap()).formula();
        let formula_cache = ic!(p = pc).already_raw().unwrap();
        InternalizedInference {
            premises,
            conclusion,
            argument_order,
            formula_cache,
        }
    }
    pub fn forget_disambiguation(&self) -> WhatWasProved {
        WhatWasProved {
            premises: self.premises.iter().cloned().collect(),
            conclusion: self.conclusion.clone(),
        }
    }
}

impl Proven<InternalizedInference> {
    pub fn weaken_to(&self, target_level: WeaknessLevel) -> Proven<InternalizedInference> {
        // get the "strong-implication of weakening" for the interior,
        let internal = self
            .formula
            .conclusion
            .weakening_implication_proof(target_level);
        // then use "strong-implication under hypotheticals"
        ProofWithPremises::imp_trans_chain(&[self.clone(), internal])
    }
}

#[derive(Clone)]
pub struct ProofWithPremises(Arc<ProofWithPremisesInner>);

pub struct ProofWithPremisesInner {
    derivation: ProofWithPremisesDerivation,
    what_was_proved_cache: WhatWasProved,
}

pub enum ProofWithPremisesDerivation {
    Premise(RWMFormula),
    WithoutPremises(ProofWithVariables),
    Rule(ProofByRule),
}

pub struct WhatWasProved {
    pub premises: BTreeSet<RWMFormula>,
    pub conclusion: WeakProposition,
}

pub struct ProofByRule {
    pub rule_instance: RuleInstance,
    pub premises: Vec<ProofWithPremises>,
}

impl Deref for ProofWithPremises {
    type Target = ProofWithPremisesInner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl From<ProofWithPremisesInner> for ProofWithPremises {
    fn from(value: ProofWithPremisesInner) -> Self {
        ProofWithPremises(Arc::new(value))
    }
}
impl Deref for ProofWithPremisesInner {
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
    pub fn weakened_by_rule(&self, rule: &Rule) -> Self {
        match rule {
            Rule::Clean(_) => self.clone(),
            Rule::Strengthening(s) => match s {
                StrengtheningRule::StrengthenSuccessor => WeaknessLevel {
                    plus_ones: self.plus_ones + 1,
                },
            },
        }
    }
    // pub fn successor(&self) -> Self {
    //     WeaknessLevel {
    //         plus_ones: self.plus_ones + 1,
    //     }
    // }
    pub fn predecessor(&self) -> Option<Self> {
        Some(WeaknessLevel {
            plus_ones: self.plus_ones.checked_sub(1)?,
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
    pub fn distribute_and(&self, a: RawFormula, b: RawFormula) -> ProofWithVariables {
        match self.predecessor() {
            None => ProofWithVariables::eq_refl(ic!(a & b).to_rwm()),
            Some(pred) => {
                let pred = pred.distribute_and(a.clone(), b.clone());
                let p = pred.conclusion().as_eq_sides().unwrap()[1].clone();
                let [wa, wb] = [a, b].map(|s| self.wrap_proposition(s.into()));
                let q = ic!(wa & wb);
                let last_step = ic!(p = q)
                    .to_rwm()
                    .prove_by_script_named("distribute_trueeq_over_and")
                    .unwrap();
                ProofWithVariables::eq_trans_chain(&[pred, last_step]).unwrap()
            }
        }
    }
}

impl RWMFormula {
    pub fn prove_by_substituting_with(
        &self,
        equivalences: &[ProofWithVariables],
    ) -> Result<ProofWithVariables, String> {
        todo((self, equivalences))
    }
    pub fn prove_by_script_named(&self, name: &str) -> Result<ProofWithVariables, String> {
        todo((self, name))
    }
    pub fn prove_by_specializing_axiom(&self) -> Result<ProofWithVariables, String> {
        todo(self)
    }
    pub fn prove_by_partially_specializing_axiom(&self) -> Result<ProofWithVariables, String> {
        todo(self)
    }
}

impl Formula {
    pub fn prove_by_substituting_with(
        &self,
        equivalences: &[ProofWithVariables],
    ) -> Result<ProofWithVariables, String> {
        self.to_rwm().prove_by_substituting_with(equivalences)
    }
    pub fn prove_by_script_named(&self, name: &str) -> Result<ProofWithVariables, String> {
        self.to_rwm().prove_by_script_named(name)
    }
    pub fn prove_by_specializing_axiom(&self) -> Result<ProofWithVariables, String> {
        self.to_rwm().prove_by_specializing_axiom()
    }
    pub fn prove_by_partially_specializing_axiom(&self) -> Result<ProofWithVariables, String> {
        self.to_rwm().prove_by_partially_specializing_axiom()
    }
}

impl WhatWasProved {
    pub fn proves(&self, inference: &InternalizedInference) -> bool {
        // can prove something weaker or with more premises
        self.premises.iter().all(|provided| {
            inference
                .premises
                .iter()
                .any(|required| required == provided)
        }) && inference.conclusion.proposition == self.conclusion.proposition
            && inference.conclusion.weakness_level >= self.conclusion.weakness_level
    }
}

impl ProofWithPremises {
    pub fn by_premise(premise: RWMFormula) -> ProofWithPremises {
        ProofWithPremisesInner {
            derivation: ProofWithPremisesDerivation::Premise(premise.clone()),
            what_was_proved_cache: WhatWasProved {
                premises: [premise.clone()].into_iter().collect(),
                conclusion: WeakProposition::new(premise, WeaknessLevel::premise()),
            },
        }
        .into()
    }
    pub fn by_rule(
        rule_premise_providers: Vec<ProofWithPremises>,
        rule_instance: RuleInstance,
    ) -> ProofWithPremises {
        let required: Vec<RWMFormula> = rule_instance.premises().collect();
        assert_eq!(
            rule_premise_providers.len(),
            required.len(),
            "wrong number of premises"
        );
        for (provider, required) in zip(&rule_premise_providers, required) {
            assert_eq!(
                provider.conclusion.proposition, required,
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
                    .map(|p| p.conclusion.weakness_level.clone())
                    .max()
                    .unwrap_or(WeaknessLevel::no_premise_used())
                    .weakened_by_rule(&rule_instance.rule),
            ),
        };
        ProofWithPremisesInner {
            derivation: ProofWithPremisesDerivation::Rule(ProofByRule {
                rule_instance,
                premises: rule_premise_providers,
            }),
            what_was_proved_cache,
        }
        .into()
    }
    // pub fn by_strengthen_successor(weak_proof: ProofWithPremises) -> ProofWithPremises {
    //     assert_eq!(
    //         weak_proof.conclusion.as_eq_sides().unwrap()[0],
    //         Formula::prop_true().to_rwm(),
    //         "proof doesn't fit by_strengthen_successor"
    //     );
    //
    //     let what_was_proved_cache = WhatWasProved {
    //         premises: weak_proof.premises.clone(),
    //         conclusion: WeakProposition::new(
    //             weak_proof.conclusion.as_eq_sides().unwrap()[1].clone(),
    //             if weak_proof.premises.is_empty() {
    //                 WeaknessLevel::no_premise_used()
    //             } else {
    //                 weak_proof.weakness_level.successor()
    //             },
    //         ),
    //     };
    //     ProofWithPremisesInner {
    //         derivation: ProofWithPremisesDerivation::StrengthenSuccessor(weak_proof),
    //         what_was_proved_cache,
    //     }
    //     .into()
    // }

    pub fn what_was_proved(&self) -> &WhatWasProved {
        &self.what_was_proved_cache
    }

    pub fn use_externally(
        &self,
        arguments: &Substitutions,
        premise_proofs: &[RawProof],
    ) -> Result<RawProof, String> {
        match &self.derivation {
            ProofWithPremisesDerivation::Premise(p) => {
                let specialized_premise = p
                    .with_metavariables_replaced_rwm(arguments)
                    .already_raw()
                    .ok_or_else(|| "Tried to use proof without specifying all arguments")?;
                premise_proofs
                    .iter()
                    .find(|premise_proof| premise_proof.conclusion() == specialized_premise)
                    .cloned()
                    .ok_or_else(|| {
                        format!("No proof of premise {} was provided", specialized_premise)
                    })
            }
            // ProofWithPremisesDerivation::CleanRule(proof) => {
            //     let instance = proof
            //         .rule_instance
            //         .further_specialize(arguments)
            //         .assume_raw();
            //     RawProof::new(
            //         instance,
            //         proof
            //             .premises
            //             .iter()
            //             .map(|p| p.use_externally(arguments, premise_proofs))
            //             .collect(),
            //     )
            // }
            // ProofWithPremisesDerivation::StrengthenSuccessor(weak_proof) => {
            //     let raw_weak_proof = weak_proof.use_externally(arguments, premise_proofs)?;
            //     if weak_proof.premises.is_empty() {
            //         RawProof::new(
            //             STRENGTHEN_SUCCESSOR.specialize().assume_raw(),
            //             vec![raw_weak_proof],
            //         )
            //     } else {
            //         raw_weak_proof
            //     }
            // }
            ProofWithPremisesDerivation::WithoutPremises(p) => p.use_externally(arguments),
            ProofWithPremisesDerivation::Rule(p) => {
                let instance = p.rule_instance.further_specialize(arguments).assume_raw();
                RawProof::new(
                    instance,
                    p.premises
                        .iter()
                        .map(|p| p.use_externally(arguments, premise_proofs))
                        .collect::<Result<_, _>>()?,
                )
            }
        }
    }
    pub fn internalize(&self, inference: &InternalizedInference) -> Proven<InternalizedInference> {
        assert!(self.what_was_proved().proves(inference));
        let result: Proven<InternalizedInference> = match &self.derivation {
            ProofWithPremisesDerivation::Premise(p) => todo(()),
            // ProofWithPremisesDerivation::CleanRule(proof) => proof.internalize(inference),
            // ProofWithPremisesDerivation::StrengthenSuccessor(weak_proof) => {
            //     if inference.premises.is_none() {
            //         // with no premises, we can do raw stuff directly
            //         let weak_result = weak_proof.internalize(&InternalizedInference::new(
            //             None,
            //             weak_proof.conclusion.unwrap(),
            //             inference.argument_order.clone(),
            //         ));
            //         weak_result.strengthen_successor()
            //     } else {
            //         // "strong True=C" is the same as "weak C", so just ask for it
            //         weak_proof.internalize(&InternalizedInference::new(
            //             inference.premises.clone(),
            //             weak_proof.conclusion.strength_predecessor().unwrap(),
            //             inference.argument_order.clone(),
            //         ))
            //     }
            // }
            ProofWithPremisesDerivation::WithoutPremises(proof) => {
                let sp = proof.internalize(inference.argument_order());
                // we now have (l=>Pl)=(l=>Ql) but we need (l=>(*=*))=(l=>(*=* & Pl=Ql))
                // i.e. we have P=Q and need (const True)=(l=>(True & (Pl=Ql)))
                let a = proof.internal_conclusion(inference.argument_order());
                let [p, q] = a.sides.clone();
                let b = formula!("l => (True & (P l=Q l))")
                    .with_metavariables_replaced_with_uncurried_functions(
                        &[("P".to_string(), p), ("Q".to_string(), q)]
                            .into_iter()
                            .collect(),
                    );
                inf!("a |- b", {a, b}).prove_by_script_named("no_premises_to_zero_premises")
            }
            ProofWithPremisesDerivation::Rule(proof) => proof.internalize(inference),
        };
        let result = result.weaken_to(inference.conclusion.weakness_level.clone());
        assert_eq!(result.conclusion(), inference.formula());
        result
    }

    pub fn imp_trans_chain(components: &[Proven<InternalizedInference>]) -> ProofWithPremises {
        todo(components)
    }
}

impl ProofByRule {
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
        // self.rule_instance.weaken(inference.weakness_level)
        todo(internal_premise_providers)
    }
}
