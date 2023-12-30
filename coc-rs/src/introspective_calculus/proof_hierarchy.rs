use crate::introspective_calculus::inference::Inference;
use crate::introspective_calculus::provers::{
    ByAssumingIt, ByAxiomSchema, ByConvertingBothSides, ByGeneralizedUnfolding,
    ByInternalIndistinguishability, ByPartiallySpecializingAxiom, ByScriptNamed,
    ByScriptWithPremises, BySpecializingAxiom, BySubstitutingWith, ByUnfolding, FormulaProver,
};
use crate::introspective_calculus::raw_proofs::{
    CleanExternalRule, CleanRule, RawProof, RawProofWeak, Rule, RuleInstance, StrengtheningRule,
};
use crate::introspective_calculus::uncurried_function::{
    UncurriedFunction, UncurriedFunctionEquivalence,
};
use crate::introspective_calculus::{
    downgrade_substitutions, Formula, FormulaWeak, RWMFormula, RawFormula, Substitutions, ToFormula,
};
use crate::{ad_hoc_lazy_static, formula, ic, substitutions};
use hash_capsule::caching::{BackrefSet, CacheMap, Downgrade, SingleCache};
use hash_capsule::{define_hash_capsule_wrappers, CapsuleContents, HashCapsuleWeak};
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Display, Formatter};
use std::iter::zip;
use std::ops::Deref;

define_hash_capsule_wrappers!(Proof, ProofWeak, ProofDerivation);

impl CapsuleContents for ProofDerivation {
    type Caches = ProofCaches;
    fn cleanup(&mut self, self_weak: HashCapsuleWeak<Self>, caches: &mut Self::Caches) {
        let self_weak = ProofWeak(self_weak);
        macro_rules! cleanup {
            ($map:ident, $backrefs: ident) => {
                caches.$map.cleanup(|input, result| {
                    if let Some(result) = result.upgrade() {
                        result.caches.$backrefs.forget(&(self_weak.clone(), input));
                    };
                });
                caches.$backrefs.cleanup(|(origin, input)| {
                    if let Some(origin) = origin.upgrade() {
                        origin.caches.$map.forget(&input);
                    };
                });
            };
        }
        cleanup!(specializations, specialization_backrefs);
        cleanup!(with_premises_satisfied, with_premises_satisfied_backrefs);
        cleanup!(generalized, generalized_backrefs);
        cleanup!(as_implications, as_implication_backrefs);
    }
}

#[derive(Default)]
pub struct ProofCaches {
    naive_size: SingleCache<u64>,
    premises: SingleCache<BTreeSet<RWMFormula>>,
    conclusion: SingleCache<RWMFormula>,

    raw_form: SingleCache<RawProofWeak>,

    specializations: CacheMap<BTreeMap<String, FormulaWeak>, ProofWeak>,
    specialization_backrefs: BackrefSet<(ProofWeak, BTreeMap<String, FormulaWeak>)>,

    with_premises_satisfied: CacheMap<Vec<ProofWeak>, ProofWeak>,
    with_premises_satisfied_backrefs: BackrefSet<(ProofWeak, Vec<ProofWeak>)>,

    generalized: CacheMap<Vec<String>, ProofWeak>,
    generalized_backrefs: BackrefSet<(ProofWeak, Vec<String>)>,

    as_implications: CacheMap<Vec<FormulaWeak>, ProofWeak>,
    as_implication_backrefs: BackrefSet<(ProofWeak, Vec<FormulaWeak>)>,
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, Serialize, Deserialize)]
pub enum ProofDerivation {
    Premise(RWMFormula),
    Rule(ProofByRule),
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, Serialize, Deserialize)]
pub struct ProofByRule {
    pub rule_instance: RuleInstance,
    pub premise_proofs: Vec<Proof>,
}

impl Display for Proof {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Inference::new(self.premises().iter().cloned().collect(), self.conclusion()).fmt(f)
    }
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct Proven<T> {
    formula: T,
    proof: Proof,
}

impl<T> Deref for Proven<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.formula
    }
}

impl<T: ToFormula> Proven<T> {
    pub fn new(formula: T, proof: Proof) -> Proven<T> {
        assert_eq!(formula.to_formula().to_rwm(), proof.conclusion());
        Proven { formula, proof }
    }
    pub fn formula(&self) -> &T {
        &self.formula
    }
    pub fn proof(&self) -> &Proof {
        &self.proof
    }
}

impl Proof {
    pub fn by_premise(premise: RWMFormula) -> Proof {
        Proof::from(ProofDerivation::Premise(premise))
    }

    pub fn by_rule(
        rule_instance: RuleInstance,
        premise_proofs: Vec<Proof>,
    ) -> Result<Proof, String> {
        let required_premises: Vec<RWMFormula> = rule_instance.premises().collect();
        if premise_proofs.len() != required_premises.len() {
            return Err(format!(
                "Wrong number of premises to rule `{}` (need {}, got {})",
                rule_instance.rule,
                required_premises.len(),
                premise_proofs.len(),
            ));
        }
        for (required, provided) in zip(&required_premises, &premise_proofs) {
            if provided.conclusion() != *required {
                return Err(format!(
                    "Incorrect premise provided to rule {} (need {required}, got {})",
                    rule_instance.rule,
                    provided.conclusion(),
                ));
            }
        }
        Ok(Proof::from(ProofDerivation::Rule(ProofByRule {
            rule_instance,
            premise_proofs,
        })))
    }

    pub fn conclusion(&self) -> RWMFormula {
        self.caches.conclusion.get(|| match &self.value {
            ProofDerivation::Premise(premise) => premise.clone(),
            ProofDerivation::Rule(proof) => proof.rule_instance.conclusion(),
        })
    }

    pub fn premises(&self) -> BTreeSet<RWMFormula> {
        self.caches.premises.get(|| match &self.value {
            ProofDerivation::Premise(premise) => [premise.clone()].into_iter().collect(),
            ProofDerivation::Rule(proof) => proof
                .premise_proofs
                .iter()
                .flat_map(Proof::premises)
                .collect(),
        })
    }

    // pub fn derivation(&self) -> &ProofDerivation {
    //     &self.derivation
    // }

    pub fn to_raw(&self) -> RawProof {
        self.caches.raw_form.get(|| self.to_raw_impl())
    }
    pub fn to_raw_impl(&self) -> RawProof {
        assert!(
            self.premises().is_empty(),
            "can only use Proof::to_raw() when there's no premises"
        );
        assert!(
            self.conclusion().is_raw(),
            "can only use Proof::to_raw() when there's no variables"
        );
        let ProofDerivation::Rule(proof) = &self.value else {
            unreachable!()
        };

        RawProof::new(
            proof.rule_instance.clone().assume_raw(),
            proof.premise_proofs.iter().map(|p| p.to_raw()).collect(),
        )
        .unwrap()
    }

    pub fn specialize(&self, arguments: &Substitutions) -> Proof {
        // use crate::introspective_calculus::solver_pool::Goal;
        // use std::cell::RefCell;
        // use std::collections::HashSet;
        // thread_local! {static PROOFS_SPECIALIZED: RefCell<HashSet<Goal>> = RefCell::new(HashSet::new());}
        // if PROOFS_SPECIALIZED.with(|g| g.borrow_mut().insert(self.to_goal())) {
        //     dbg!(
        //         PROOFS_SPECIALIZED.with(|g| g.borrow().len()),
        //         self.to_goal()
        //     );
        //     if PROOFS_SPECIALIZED.with(|g| g.borrow().len()) > 30 {
        //         panic!()
        //     }
        // }
        // self.specialize_impl(arguments, &mut Default::default())
        let downgraded = downgrade_substitutions(arguments);
        let result = self
            .caches
            .specializations
            .get(downgraded.clone(), || self.specialize_impl(arguments));
        result
            .caches
            .specialization_backrefs
            .insert((self.downgrade(), downgraded));
        result
    }
    pub fn specialize_impl(&self, arguments: &Substitutions) -> Proof {
        match &self.value {
            ProofDerivation::Premise(premise) => {
                Proof::by_premise(premise.with_metavariables_replaced_rwm(arguments))
            }
            ProofDerivation::Rule(proof) => Proof::by_rule(
                proof.rule_instance.further_specialize(arguments),
                proof
                    .premise_proofs
                    .iter()
                    .map(|p| p.specialize(arguments))
                    .collect(),
            )
            .unwrap(),
        }
    }

    pub fn satisfy_premises_with(&self, premise_proofs: &[Proof]) -> Proof {
        let downgraded: Vec<ProofWeak> = premise_proofs.iter().map(Downgrade::downgrade).collect();
        let result = self
            .caches
            .with_premises_satisfied
            .get(downgraded.clone(), || {
                self.satisfy_premises_with_impl(premise_proofs)
            });
        result
            .caches
            .with_premises_satisfied_backrefs
            .insert((self.downgrade(), downgraded));
        result
    }
    pub fn satisfy_premises_with_impl(&self, premise_proofs: &[Proof]) -> Proof {
        match &self.value {
            ProofDerivation::Premise(p) => {
                for premise_proof in premise_proofs {
                    if p == &premise_proof.conclusion() {
                        return premise_proof.clone();
                    }
                }
                self.clone()
            }
            ProofDerivation::Rule(proof) => Proof::by_rule(
                proof.rule_instance.clone(),
                proof
                    .premise_proofs
                    .iter()
                    .map(|p| p.satisfy_premises_with(premise_proofs))
                    .collect(),
            )
            .unwrap(),
        }
    }

    pub fn use_externally(
        &self,
        arguments: &Substitutions,
        premise_proofs: &[RawProof],
    ) -> RawProof {
        self.specialize(arguments)
            .satisfy_premises_with(
                &premise_proofs
                    .iter()
                    .map(RawProof::to_fancy_proof)
                    .collect_vec(),
            )
            .to_raw()
    }
    // fn internal_conclusion(&self, argument_order: &[String]) -> UncurriedFunctionEquivalence {
    //     UncurriedFunctionEquivalence {
    //         sides: self
    //             .conclusion()
    //             .as_eq_sides()
    //             .unwrap()
    //             .map(|s| s.to_uncurried_function_of(argument_order)),
    //     }
    // }

    // Replace each premise and conclusion of this proof with uncurried functions, such that the given variables are eliminated and replaced with list-member-usages.
    //
    // If there are no premises, this gives a proof that is an equivalent, internalized form. If premises do exist, then the resulting proof is "less powerful". (Effectively, you start with `(∀x, Px -> Qx)` but are left with only `(∀x, Px) -> (∀x, Qx)`.)
    pub fn variables_to_internalized_argument_list(
        &self,
        argument_order: &[String],
    ) -> Proven<UncurriedFunctionEquivalence> {
        let result = self.caches.generalized.get(argument_order.to_owned(), || {
            self.variables_to_internalized_argument_list_impl(argument_order)
        });
        result
            .caches
            .generalized_backrefs
            .insert((self.downgrade(), argument_order.to_owned()));
        Proven::new(
            self.conclusion()
                .to_uncurried_function_equivalence(argument_order)
                .unwrap(),
            result,
        )
    }
    pub fn variables_to_internalized_argument_list_impl(&self, argument_order: &[String]) -> Proof {
        let conclusion = self
            .conclusion()
            .to_uncurried_function_equivalence(argument_order)
            .unwrap();
        match &self.value {
            ProofDerivation::Premise(_) => conclusion.formula().prove(ByAssumingIt),
            ProofDerivation::Rule(proof) => {
                let premise_proofs: Vec<Proven<UncurriedFunctionEquivalence>> = proof
                    .premise_proofs
                    .iter()
                    .map(|p| p.variables_to_internalized_argument_list(argument_order))
                    .collect();

                match &proof.rule_instance.rule {
                    Rule::Clean(CleanRule::External(c)) => match c {
                        CleanExternalRule::EqSym => premise_proofs[0].flip().proof().clone(),
                        CleanExternalRule::EqTrans => {
                            Proven::<UncurriedFunctionEquivalence>::trans_chain(&premise_proofs)
                                .unwrap()
                                .proof()
                                .clone()
                        }
                        CleanExternalRule::DefinitionOfConst
                        | CleanExternalRule::DefinitionOfFuse => {
                            // dbg!(self.to_goal());
                            // dbg!(self.conclusion());
                            // eprintln!("{conclusion}");
                            conclusion.formula().prove(ByPartiallySpecializingAxiom)
                        }
                        CleanExternalRule::SubstituteInLhs | CleanExternalRule::SubstituteInRhs => {
                            conclusion.formula().prove(BySubstitutingWith(
                                &premise_proofs
                                    .iter()
                                    .map(|p| p.proof().clone())
                                    .collect_vec(),
                            ))
                        }
                        CleanExternalRule::SubstituteInConjunction => {
                            // We have a double-generalized premise provider, we need to convert it to pair form, then apply SubstituteInConjunction, then unpair again to get the result

                            // let proof_with_original_metavariables = ad_hoc_lazy_static!(Proven<UncurriedFunctionEquivalence>)(|| {
                            //
                            // });
                            //
                            // proof_with_original_metavariables.specialize()

                            let batch = |f: RawFormula| {
                                ad_hoc_lazy_static!(RWMFormula)(|| {
                                    formula!(
                                        "fuse (fuse (const f) a) b",
                                        {
                                            a: UncurriedFunction::nth_argument(0).formula(),
                                            b: UncurriedFunction::nth_argument(1).formula(),
                                        }
                                    )
                                    .to_rwm()
                                })
                                .with_metavariables_replaced_rwm(&substitutions! {f})
                                .to_raw()
                                .unwrap()
                            };
                            let unbatch = |f: RawFormula| {
                                ic!("a" => ("b" => (f ("a", ("b", {Formula::default()}))))).to_rwm()
                            };
                            let pairify = |eq: &UncurriedFunctionEquivalence| {
                                eq.sides.each_ref().map(|s| batch(s.formula()))
                            };
                            let [x, y] = pairify(&premise_proofs[0].formula);
                            let [z, w] = pairify(&conclusion);
                            let adapted_premise = ic!(x = y)
                                .prove(BySubstitutingWith(&[premise_proofs[0].proof().clone()]));
                            let rule_instance =
                                Rule::from(CleanExternalRule::SubstituteInConjunction).specialize(
                                    proof
                                        .rule_instance
                                        .substitutions
                                        .iter()
                                        .map(|(name, value)| {
                                            (
                                                name.clone(),
                                                batch(
                                                    value
                                                        .to_uncurried_function_of(argument_order)
                                                        .formula(),
                                                )
                                                .to_rwm(),
                                            )
                                        })
                                        .collect(),
                                );
                            let adapted_premise = rule_instance.premises().next().unwrap().prove(
                                ByConvertingBothSides(&adapted_premise, ByGeneralizedUnfolding),
                            );
                            let adapted_conclusion =
                                Proof::by_rule(rule_instance, vec![adapted_premise]).unwrap();
                            let adapted_conclusion = ic!(z = w).prove(ByConvertingBothSides(
                                &adapted_conclusion,
                                ByGeneralizedUnfolding,
                            ));
                            let adapted_conclusion = ic!({ unbatch(z) } = { unbatch(w) })
                                .prove(BySubstitutingWith(&[adapted_conclusion]));
                            conclusion
                                .formula()
                                .prove(ByConvertingBothSides(&adapted_conclusion, ByUnfolding))
                        }
                    },
                    Rule::Clean(CleanRule::Axiom(axiom)) => {
                        // The axiom guarantees a=b, and
                        // since these are raw formulas, only one value of `conclusion` is possible, and it's extensionally equal to const a = const b
                        //assert_eq!(todo(()),todo(()));
                        let result = axiom.generalized_proof();
                        assert_eq!(result.formula, conclusion);
                        result.proof().clone()
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
                            // conclusion
                            //     .prove(ByScriptNamed("generalize_strengthen_successor"))
                            unimplemented!("weakness")
                        }
                    },
                }
            }
        }
    }

    pub fn eq_refl(a: RWMFormula) -> Proof {
        //ic!(a = a).prove(ByScriptNamed("eq_refl"))
        let p = formula!("const a const = a", { a }).prove(ByAxiomSchema);
        Proof::eq_trans_chain(&[p.flip_conclusion(), p]).unwrap()
    }

    pub fn flip_conclusion(&self) -> Proof {
        let [a, b] = self.conclusion().as_eq_sides().unwrap();
        Proof::by_rule(
            Rule::from(CleanExternalRule::EqSym).specialize(substitutions! {A:a,B:b}),
            vec![self.clone()],
        )
        .unwrap()
    }

    pub fn eq_trans_chain(components: &[Proof]) -> Result<Proof, String> {
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
            result = Proof::by_rule(
                Rule::from(CleanExternalRule::EqTrans)
                    .specialize(substitutions! {A: a, B: b1, C: c}),
                vec![result, inference.clone()],
            )
            .unwrap()
        }
        Ok(result)
    }

    pub fn naive_size(&self) -> u64 {
        self.caches.naive_size.get(|| match &self.value {
            ProofDerivation::Premise(p) => p.naive_size(),
            ProofDerivation::Rule(r) => {
                let mut result = r.rule_instance.conclusion().naive_size();
                for f in r.rule_instance.premises() {
                    result = result.saturating_add(f.naive_size());
                }
                for f in &r.premise_proofs {
                    result = result.saturating_add(f.naive_size());
                }
                result
            }
        })
    }
}

// #[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
// pub struct WeaknessLevel {
//     // later to be extended to ordinals
//     // plus_omegas: usize,
//     plus_ones: usize,
// }
// impl WeaknessLevel {
//     pub fn no_premise_used() -> Self {
//         WeaknessLevel { plus_ones: 0 }
//     }
//     pub fn premise() -> Self {
//         WeaknessLevel { plus_ones: 0 }
//     }
//     pub fn weakened_by_rule(&self, rule: &Rule) -> Self {
//         match rule {
//             Rule::Clean(_) => self.clone(),
//             Rule::Strengthening(s) => match s {
//                 StrengtheningRule::StrengthenSuccessor => WeaknessLevel {
//                     plus_ones: self.plus_ones + 1,
//                 },
//             },
//         }
//     }
//     // pub fn successor(&self) -> Self {
//     //     WeaknessLevel {
//     //         plus_ones: self.plus_ones + 1,
//     //     }
//     // }
//     pub fn predecessor(&self) -> Option<Self> {
//         Some(WeaknessLevel {
//             plus_ones: self.plus_ones.checked_sub(1)?,
//         })
//     }
//     // pub fn successors_of_members(&self) -> Self {
//     //     match *(self.0) {
//     //         WeaknessLevelInner::Successor(_) => self.successor(),
//     //         _ => self.clone(),
//     //     }
//     // }
//
//     pub fn wrap_proposition(&self, proposition: Formula) -> Formula {
//         match self.predecessor() {
//             None => proposition,
//             Some(n) => {
//                 ic!(True = { n.wrap_proposition(proposition) })
//             }
//         }
//     }
//
//     // return (weak(A) and weak(B)) = weak(A and B)
//     pub fn distribute_and(&self, a: RawFormula, b: RawFormula) -> ProofWithVariables {
//         match self.predecessor() {
//             None => ProofWithVariables::eq_refl(ic!(a & b).to_rwm()),
//             Some(pred) => {
//                 let pred = pred.distribute_and(a.clone(), b.clone());
//                 let p = pred.conclusion().as_eq_sides().unwrap()[1].clone();
//                 let [wa, wb] = [a, b].map(|s| self.wrap_proposition(s.into()));
//                 let q = ic!(wa & wb);
//                 let last_step = ic!(p = q)
//                     .to_rwm()
//                     .prove(ByScriptNamed("distribute_trueeq_over_and"));
//                 ProofWithVariables::eq_trans_chain(&[pred, last_step]).unwrap()
//             }
//         }
//     }
// }

// #[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
// pub struct WeakProposition {
//     proposition: RWMFormula,
//     weakness_level: WeaknessLevel,
//     formula_cache: RWMFormula,
// }

// impl WeakProposition {
//     pub fn new(proposition: RWMFormula, weakness_level: WeaknessLevel) -> WeakProposition {
//         let formula_cache = weakness_level
//             .wrap_proposition(proposition.to_formula())
//             .to_rwm();
//         WeakProposition {
//             proposition,
//             weakness_level,
//             formula_cache,
//         }
//     }
//
//     pub fn proposition(&self) -> F {
//         self.proposition.clone()
//     }
//
//     pub fn weakness_level(&self) -> WeaknessLevel {
//         self.weakness_level.clone()
//     }
//
//     pub fn formula(&self) -> RWMFormula {
//         self.formula_cache.clone()
//     }
//
//     pub fn weaken_to(&self, target_level: WeaknessLevel) -> WeakProposition {
//         assert!(target_level >= self.weakness_level);
//         WeakProposition::new(self.proposition.clone(), target_level)
//     }
//     pub fn strength_predecessor(&self) -> Option<WeakProposition> {
//         Some(WeakProposition::new(
//             self.proposition.clone(),
//             self.weakness_level.predecessor()?,
//         ))
//     }
//
//     // pub fn weakening_implication_proof(&self, target_level: WeaknessLevel) -> Proof {
//     //     assert!(target_level >= self.weakness_level);
//     //     if target_level == self.weakness_level {
//     //         Proof::imp_refl()
//     //     } else {
//     //         let pred = self.weakening_implication_proof(target_level.predecessor().unwrap());
//     //         // we have:
//     //         // (self -> pred)
//     //         //
//     //         Proof::imp_trans(pred, "true_equals_intro")
//     //     }
//     // }
// }

// impl Proven<WeakProposition> {
//     pub fn weaken_to(&self, target_level: WeaknessLevel) -> Proven<WeakProposition> {
//         assert!(target_level >= self.formula.weakness_level);
//         if target_level == self.formula.weakness_level {
//             self.clone()
//         } else {
//             let pred = self.weaken_to(self.formula.weakness_level.predecessor().unwrap());
//             Proven::new(
//                 WeakProposition::new(self.formula.proposition.clone(), target_level),
//                 Proof::uhh("true_equals_intro", pred.proof),
//             )
//         }
//     }
// }

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct InferenceAsEquivalence {
    premises: Vec<RWMFormula>,
    conclusion: RWMFormula,
    //argument_order: Vec<String>,
    formula_cache: RWMFormula,
}

impl ToFormula for InferenceAsEquivalence {
    fn to_formula(&self) -> Formula {
        self.formula().to_formula()
    }
}

impl InferenceAsEquivalence {
    pub fn premises(&self) -> &Vec<RWMFormula> {
        &self.premises
    }
    pub fn conclusion(&self) -> &RWMFormula {
        &self.conclusion
    }
    // pub fn argument_order(&self) -> &Vec<String> {
    //     &self.argument_order
    // }
    pub fn formula(&self) -> &RWMFormula {
        &self.formula_cache
    }

    pub fn new(
        premises: Vec<RWMFormula>,
        conclusion: RWMFormula,
        // argument_order: Vec<String>,
    ) -> InferenceAsEquivalence {
        // let to_fn = |f: &Formula| f.to_rwm().to_uncurried_function_of(&argument_order);
        let p = Formula::and_and_true(&premises.iter().map(|f| f.to_formula()).collect::<Vec<_>>())
            .unwrap();
        let pc = Formula::and([p.clone(), conclusion.to_formula()]).unwrap();
        let formula_cache = ic!(p = pc).to_rwm();
        InferenceAsEquivalence {
            premises,
            conclusion,
            // argument_order,
            formula_cache,
        }
    }
    pub fn from_inference(inference: Inference) -> InferenceAsEquivalence {
        InferenceAsEquivalence::new(inference.premises.clone(), inference.conclusion.clone())
    }
    // pub fn forget_disambiguation(&self) -> WhatWasProved {
    //     WhatWasProved {
    //         premises: self.premises.iter().cloned().collect(),
    //         conclusion: self.conclusion.clone(),
    //     }
    // }

    pub fn prove(&self, how: impl FormulaProver) -> Proven<InferenceAsEquivalence> {
        Proven::new(self.clone(), self.formula().prove(how))
    }
}
//
// impl Proven<InternalInference> {
//     pub fn weaken_to(&self, target_level: WeaknessLevel) -> Proven<InternalInference> {
//         // get the "strong-implication of weakening" for the interior,
//         let internal = self
//             .formula
//             .conclusion
//             .weakening_implication_proof(target_level);
//         // then use "strong-implication under hypotheticals"
//         Proof::imp_trans_chain(&[self.clone(), internal])
//     }
// }
//

// #[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
// pub struct HowToInternalizeInference {
//     premise_order: Vec<RWMFormula>,
//     // argument_order: Vec<String>,
//     // weakness_level: WeaknessLevel,
// }
//
// impl HowToInternalizeInference {
//     pub fn internalize(&self, what: &WhatWasProved) -> InferenceAsEquivalence {
//         assert!(what.premises.iter().all(|required| {
//             self.premise_order
//                 .iter()
//                 .any(|provided| provided == required)
//         }));
//         // assert!(self.weakness_level >= what.conclusion.weakness_level());
//         let premises = self
//             .premise_order
//             .iter()
//             .map(|premise| {
//                 premise
//                     // .to_uncurried_function_equivalence(&self.argument_order)
//                     .clone()
//             })
//             .collect();
//         // let conclusion = WeakProposition::new(
//         //     what.conclusion
//         //         .formula()
//         //         // .to_uncurried_function_equivalence(&self.argument_order)
//         //         .unwrap(),
//         //     what.conclusion.weakness_level()
//         //     // self.weakness_level,
//         // );
//         let conclusion = what.conclusion.clone();
//         InferenceAsEquivalence::new(premises, conclusion)
//     }
// }
//
//
// impl WhatWasProved {
//     pub fn proves(&self, inference: &InternalInference) -> bool {
//         // can prove something weaker or with more premises
//         self.premises.iter().all(|provided| {
//             inference
//                 .premises
//                 .iter()
//                 .any(|required| required == provided)
//         }) && inference.conclusion.proposition == self.conclusion.proposition
//             && inference.conclusion.weakness_level >= self.conclusion.weakness_level
//     }
// }

impl CleanRule {
    pub fn premises_to_internal_implication(
        &self,
        instance: &RuleInstance,
    ) -> Proven<InferenceAsEquivalence> {
        let goal =
            InferenceAsEquivalence::new(instance.premises().collect(), instance.conclusion());
        match self {
            CleanRule::External(rule) => match rule {
                CleanExternalRule::EqSym => goal.prove(ByScriptNamed("intinf_eq_sym")),
                CleanExternalRule::EqTrans => goal.prove(ByScriptNamed("intinf_eq_trans")),
                CleanExternalRule::SubstituteInLhs => goal.prove(ByScriptNamed("intinf_subst_lhs")),
                CleanExternalRule::SubstituteInRhs => goal.prove(ByScriptNamed("intinf_subst_rhs")),
                CleanExternalRule::SubstituteInConjunction => {
                    goal.prove(ByScriptNamed("intinf_subst_conj"))
                }
                _ => goal.prove(ByScriptNamed("inject_tautology_under_hypothetical")),
            },
            CleanRule::Axiom(_) => goal.prove(ByScriptNamed("inject_tautology_under_hypothetical")),
        }
    }
}

impl Proof {
    // pub fn by_strengthen_successor(weak_proof: Proof) -> Proof {
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

    pub fn premises_to_internal_implication(
        &self,
        premise_order: &[RWMFormula],
    ) -> Proven<InferenceAsEquivalence> {
        let downgraded: Vec<FormulaWeak> = premise_order.iter().map(Downgrade::downgrade).collect();
        let result = self.caches.as_implications.get(downgraded.clone(), || {
            self.premises_to_internal_implication_impl(premise_order)
        });
        result
            .caches
            .as_implication_backrefs
            .insert((self.downgrade(), downgraded));
        Proven::new(
            InferenceAsEquivalence::new(premise_order.to_owned(), self.conclusion()),
            result,
        )
    }
    pub fn premises_to_internal_implication_impl(&self, premise_order: &[RWMFormula]) -> Proof {
        for premise in self.premises() {
            assert!(premise_order.contains(&premise));
        }
        let goal = InferenceAsEquivalence::new(premise_order.to_owned(), self.conclusion())
            .formula()
            .clone();
        let [gl, _gr] = goal.as_eq_sides().unwrap();
        let result: Proof = match &self.value {
            ProofDerivation::Premise(conclusion) => {
                // let [gll,glr]=gl.as_eq_sides().unwrap();
                let extractor = UncurriedFunction::nth_argument(
                    premise_order.iter().position(|p| p == conclusion).unwrap(),
                )
                .formula()
                .to_rwm();
                goal.prove(ByInternalIndistinguishability {
                    equivalence: gl,
                    extractor,
                })
            }
            // ProofWithPremisesDerivation::CleanRule(proof) => proof.internalize(inference),
            // ProofWithPremisesDerivation::StrengthenSuccessor(weak_proof) => {
            //     if inference.premises.is_none() {
            //         // with no premises, we can do raw stuff directly
            //         let weak_result = weak_proof.internalize(&InternalInference::new(
            //             None,
            //             weak_proof.conclusion.unwrap(),
            //             inference.argument_order.clone(),
            //         ));
            //         weak_result.strengthen_successor()
            //     } else {
            //         // "strong True=C" is the same as "weak C", so just ask for it
            //         weak_proof.internalize(&InternalInference::new(
            //             inference.premises.clone(),
            //             weak_proof.conclusion.strength_predecessor().unwrap(),
            //             inference.argument_order.clone(),
            //         ))
            //     }
            // }
            // ProofWithPremisesDerivation::WithoutPremises(proof) => {
            //     // let sp = proof.to_uncurried_function_equivalence(&how.argument_order);
            //     // // we now have (l=>Pl)=(l=>Ql) but we need (l=>(*=*))=(l=>(*=* & Pl=Ql))
            //     // // i.e. we have P=Q and need (const True)=(l=>(True & (Pl=Ql)))
            //     // // let a = proof.internal_conclusion(&how.argument_order);
            //     // let [p, q] = sp.sides.clone();
            //     // let b = formula!("(P=Q) & True")
            //     //     .with_metavariables_replaced_with_uncurried_functions(
            //     //         &[("P".to_string(), p), ("Q".to_string(), q)]
            //     //             .into_iter()
            //     //             .collect(),
            //     //     );
            //     // inf!("a |- b", {a, b}).prove(ByScriptNamed("no_premises_to_zero_premises"))
            //     Proven::new(goal, proof.clone())
            // }
            ProofDerivation::Rule(proof) => {
                let mut internal_premise_providers = proof
                    .premise_proofs
                    .iter()
                    .map(|p| p.premises_to_internal_implication(premise_order));
                match &proof.rule_instance.rule {
                    Rule::Clean(rule) => {
                        // let internal_premise_providers = internal_premise_providers
                        //     .map(|p| p.weaken_to(self.what_was_proved().conclusion.weakness_level()));
                        match internal_premise_providers.len() {
                            0 => goal.prove(ByScriptWithPremises(
                                "inject_tautology_under_hypothetical",
                                &[self.clone()],
                            )),
                            1 => {
                                // we have a proof of P -> A (the premise), and another of A -> B (the rule)
                                // let rule_implication =
                                //     rule.premises_to_internal_implication(&proof.rule_instance);
                                // goal.prove(ByScriptWithPremises(
                                //     "imp_trans",
                                //     &[
                                //         internal_premise_providers.next().unwrap().proof().clone(),
                                //         rule_implication.proof().clone(),
                                //     ],
                                // ))
                                let premise_provider = internal_premise_providers.next().unwrap();
                                let rule_implication =
                                    ic!({premise_provider.conclusion()} -> {self.conclusion()});
                                let rule_implication = if matches!(
                                    rule,
                                    CleanRule::External(CleanExternalRule::SubstituteInLhs)
                                ) {
                                    // dbg!(&rule_implication);
                                    rule_implication.prove(ByScriptNamed("internal_specialization"))
                                } else {
                                    rule_implication.prove(BySpecializingAxiom)
                                };
                                goal.prove(ByScriptWithPremises(
                                    "imp_trans",
                                    &[premise_provider.proof().clone(), rule_implication],
                                ))
                            }
                            2 => {
                                // the only binary rule is eq_trans, so we have a proof of P -> (A = B) and another of P -> (B = C)
                                goal.prove(ByScriptWithPremises(
                                    "eq_trans_under_hypothetical",
                                    &[
                                        internal_premise_providers.next().unwrap().proof().clone(),
                                        internal_premise_providers.next().unwrap().proof().clone(),
                                    ],
                                ))
                            }
                            _ => unreachable!("no rule has more than 2 premises"),
                        }
                    }
                    Rule::Strengthening(_) => {
                        // "strong True=C" is the same as "weak C", so just use the same proof directly
                        // let subresult = internal_premise_providers.next().unwrap();
                        // Proven::new(goal, subresult.proof().clone())
                        unimplemented!("weakness")
                    }
                }
            }
        };
        // let result = result.weaken_to(inference.conclusion.weakness_level.clone());
        assert_eq!(result.conclusion(), goal.to_rwm());
        result
    }

    // pub fn imp_trans_chain(components: &[Proven<InferenceAsEquivalence>]) -> Proof {
    //     todo(components)
    // }
}

// impl ProofByRule {
//     pub fn internalize(&self, how: &HowToInternalizeInference) -> Proven<InferenceAsEquivalence> {
//         let internal_premise_providers = self.premises.iter().map(|p| {
//             p.to_equivalence(&how)
//         });
//         if matches!(self.rule_instance.rule, Rule::Strengthening(_)) {
//             let subresult = internal_premise_providers.next().unwrap();
//             Proven::new(how.internalize(){
//                 premises: subresult.premises.,
//                 conclusion: WeakProposition {},
//                 formula_cache: Default::default()
//                     ..subresult.formula().clone()
//             })
//             subresult.proof().clone()
//         }
//         else {
//
//             .weaken_to(self.)
//         }
//         // we now have, e.g.:
//         // (P=Q) -> (True = (A=B))   (i.e. (x=>(P=Q)) = (x=>(P, True)=(Q, (A=B))))
//         // (P=Q) -> (True = (C=D))    "
//         // and the rule,
//         // (A=B), (C=D) |- (E=F)
//         // which internalizes to
//         // (x => ((*, x[0]), x[2]) = ((*, x[1]), x[3]))
//         // = (x => (((*, x[0]), x[2]), x[4]) = (((*, x[1]), x[3]), x[4]))
//         // basic idea is:
//         // spawn all premises, to get P = P and ((weak A) and (weak C))
//         // apply weak-and distribution, get P = P and weak (A and C)
//         // partially specialize the rule to get (A and C) = (A and C) and E
//         // substitute
//         // then despawn all premises
//         // self.rule_instance.weaken(inference.weakness_level)
//         todo(internal_premise_providers)
//     }
// }
