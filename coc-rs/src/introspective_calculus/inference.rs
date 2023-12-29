use crate::display::DisplayItem;
use crate::ic;
use crate::introspective_calculus::{Formula, ToFormula};
use crate::introspective_calculus::{ProofLineParser, RWMFormula};
use anyhow::anyhow;
use arrayvec::ArrayVec;
use std::collections::BTreeSet;
use std::fmt::{Display, Formatter};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::iter::once;
use std::ops::Deref;
use std::path::Path;
use std::sync::Arc;

#[derive(Debug)]
pub enum FormulaOrImplicitEquality {
    Formula(Formula),
    ImplicitEquality(Formula),
    StartEqChain(Formula),
}

impl Default for FormulaOrImplicitEquality {
    fn default() -> Self {
        FormulaOrImplicitEquality::Formula(Default::default())
    }
}

#[derive(Debug, Default)]
pub struct ProofLine {
    pub name: String,
    pub formula: FormulaOrImplicitEquality,
    pub referents: ArrayVec<String, 2>,
    pub deriver_name: Option<String>,
}

// everything in the same derivation tree is using the same metavariable identities
// here we specify the _parameters_ to the rules (as opposed to the premises/conclusions)
// #[derive(Debug)]
// pub enum InferenceDerivation {
//     Rule {
//         rule: Rule,
//         substitutions: Substitutions,
//     },
//     Premise(usize),
//     Chain(Vec<ProvenInference>, ProvenInference),
// }

#[derive(Clone, Debug)]
pub struct Inference(Arc<InferenceInner>);
#[derive(Debug)]
pub struct InferenceInner {
    pub premises: Vec<RWMFormula>,
    pub conclusion: RWMFormula,
}

#[derive(Debug)]
pub struct NamedPrettyInference {
    pub name: String,
    pub inference: PrettyInference,
}

#[derive(Clone, Debug)]
pub struct PrettyInference(Arc<PrettyInferenceInner>);
#[derive(Debug)]
pub struct PrettyInferenceInner {
    pub premises: Vec<Formula>,
    pub conclusion: Formula,
}

// #[derive(Clone, Debug)]
// pub struct ProvenInference(Arc<ProvenInferenceInner>);
// #[derive(Debug)]
// pub struct ProvenInferenceInner {
//     inference: Inference,
//     derivation: InferenceDerivation,
// }

impl Display for Inference {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some((last, rest)) = self.premises.split_last() {
            for premise in rest {
                premise.to_display_item(false).display_one_liner().fmt(f)?;
                ", ".fmt(f)?;
            }
            last.to_display_item(false).display_one_liner().fmt(f)?;
            " ".fmt(f)?;
        }
        write!(
            f,
            "|- {}",
            self.conclusion.to_display_item(false).display_one_liner()
        )
    }
}

impl Deref for Inference {
    type Target = InferenceInner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Display for PrettyInference {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some((last, rest)) = self.premises.split_last() {
            for premise in rest {
                premise.fmt(f)?;
                ", ".fmt(f)?;
            }
            last.fmt(f)?;
            " ".fmt(f)?;
        }
        write!(f, "|- {}", self.conclusion)
    }
}

impl Deref for PrettyInference {
    type Target = PrettyInferenceInner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

// impl Display for ProvenInference {
//     fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
//         self.inference.fmt(f)
//     }
// }
//
// impl Deref for ProvenInference {
//     type Target = ProvenInferenceInner;
//
//     fn deref(&self) -> &Self::Target {
//         &self.0
//     }
// }
//
// impl Deref for ProvenInferenceInner {
//     type Target = Inference;
//
//     fn deref(&self) -> &Self::Target {
//         &self.inference
//     }
// }

impl From<PrettyInferenceInner> for PrettyInference {
    fn from(value: PrettyInferenceInner) -> Self {
        PrettyInference(Arc::new(value))
    }
}

impl From<InferenceInner> for Inference {
    fn from(value: InferenceInner) -> Self {
        Inference(Arc::new(value))
    }
}

// impl From<ProvenInferenceInner> for ProvenInference {
//     fn from(value: ProvenInferenceInner) -> Self {
//         ProvenInference(Arc::new(value))
//     }
// }

impl PrettyInference {
    // pub fn new(name: String, premises: Vec<Formula>, conclusion: Formula) -> PrettyInference {
    //     PrettyInferenceInner {
    //         name,
    //         premises,
    //         conclusion,
    //     }
    //     .into()
    // }

    pub fn to_rwm(&self) -> Inference {
        InferenceInner {
            premises: self.premises.iter().map(Formula::to_rwm).collect(),
            conclusion: self.conclusion.to_rwm(),
        }
        .into()
    }

    // pub fn tuple_equality_form(&self) -> [TupleEqualityTree<Formula>; 2] {
    //     [
    //         TupleEqualityTree::Tuple(
    //             self.premises
    //                 .iter()
    //                 .map(|p| TupleEqualityTree::Element(p.as_eq_sides().unwrap()))
    //                 .collect(),
    //         ),
    //         TupleEqualityTree::Tuple(
    //             self.premises
    //                 .iter()
    //                 .chain(once(&self.conclusion))
    //                 .map(|p| TupleEqualityTree::Element(p.as_eq_sides().unwrap()))
    //                 .collect(),
    //         ),
    //     ]
    // }

    pub fn metavariables_to_arguments(&self, arguments: &[String]) -> PrettyInference {
        let fix = |f: &Formula| {
            let [l, r] = f
                .as_eq_sides()
                .unwrap()
                .map(|f| f.metavariables_to_arguments(arguments));
            ic!(l = r)
        };

        PrettyInferenceInner {
            premises: self.premises.iter().map(fix).collect(),
            conclusion: fix(&self.conclusion),
        }
        .into()
    }
}

impl Inference {
    pub fn new(premises: Vec<RWMFormula>, conclusion: RWMFormula) -> Inference {
        InferenceInner {
            premises,
            conclusion,
        }
        .into()
    }
    pub fn to_pretty(&self) -> PrettyInference {
        PrettyInferenceInner {
            premises: self.premises.iter().map(Formula::from).collect(),
            conclusion: self.conclusion.to_formula(),
        }
        .into()
    }
    // pub fn tuple_equality_form(&self) -> [TupleEqualityTree<RWMFormula>; 2] {
    //     self.to_pretty().tuple_equality_form().map(|t| t.to_rwm())
    // }
    pub fn metavariables_to_arguments(&self, arguments: &[String]) -> Inference {
        self.to_pretty()
            .metavariables_to_arguments(arguments)
            .to_rwm()
    }

    pub fn free_metavariables(&self) -> BTreeSet<String> {
        self.premises
            .iter()
            .chain(once(&self.conclusion))
            .flat_map(|f| f.free_metavariables())
            .cloned()
            .collect()
    }

    pub fn naive_size(&self) -> u64 {
        self.premises
            .iter()
            .chain(once(&self.conclusion))
            .map(|f| f.naive_size())
            .sum()
    }
}

// #[live_prop_test]
// impl ProvenInference {
//     pub fn derivation(&self) -> &InferenceDerivation {
//         &self.derivation
//     }
//     pub fn specialize(&self, arguments: &Substitutions) -> ProvenInference {
//         ProvenInferenceInner {
//             inference: Inference::new(
//                 self.premises
//                     .iter()
//                     .map(|p| p.with_metavariables_replaced_rwm(arguments))
//                     .collect(),
//                 self.conclusion.with_metavariables_replaced_rwm(arguments),
//             ),
//             derivation: match &self.derivation {
//                 InferenceDerivation::Rule {
//                     rule,
//                     substitutions,
//                 } => InferenceDerivation::Rule {
//                     rule: rule.clone(),
//                     // remember that the arguments are for the variables of self, which are the ones used *inside* `substitutions`, rather than those of the rule
//                     substitutions: substitutions
//                         .iter()
//                         .map(|(k, v)| (k.clone(), v.with_metavariables_replaced_rwm(arguments)))
//                         .collect(),
//                 },
//                 InferenceDerivation::Premise(which) => InferenceDerivation::Premise(*which),
//                 InferenceDerivation::Chain(premise_providers, conclusion_provider) => {
//                     InferenceDerivation::Chain(
//                         premise_providers
//                             .iter()
//                             .map(|p| p.specialize(arguments))
//                             .collect(),
//                         conclusion_provider.specialize(arguments),
//                     )
//                 }
//             },
//         }
//         .into()
//     }
//     // pub fn apply(&self, premises: &[&TrueFormula]) -> Result<TrueFormula, String> {
//     //     if premises.len() != self.premises.len() {
//     //         return Err(format!(
//     //             "Wrong number of premises given for inference `{self}` (given {}, needs {})",
//     //             premises.len(),
//     //             self.premises.len()
//     //         ));
//     //     }
//     //     for (required, &provided) in zip(&self.premises, premises) {
//     //         let Some(required) = required.already_raw() else {
//     //             return Err(format!("required premise {required} wasn't already raw"));
//     //         };
//     //         if **provided != required {
//     //             return Err(format!(
//     //                 "provided premise {} did not match the required premise {}",
//     //                 provided.formula(),
//     //                 required
//     //             ));
//     //         }
//     //     }
//     //     match &self.derivation {
//     //         InferenceDerivation::Premise(which) => Ok(premises[*which].clone()),
//     //         InferenceDerivation::Axiom(axiom) => Ok(TrueFormula::axiom(axiom.clone())),
//     //         InferenceDerivation::SingleRule(rule) => Ok(rule.apply(premises).unwrap()),
//     //         InferenceDerivation::Chain(premise_providers, conclusion_provider) => {
//     //             let intermediate_premises: Vec<TrueFormula> = premise_providers
//     //                 .iter()
//     //                 .map(|p| p.apply(premises).unwrap())
//     //                 .collect();
//     //             Ok(conclusion_provider
//     //                 .apply(&intermediate_premises.iter().collect_vec())
//     //                 .unwrap())
//     //         }
//     //     }
//     // }
//
//     pub fn rule(rule: Rule) -> ProvenInference {
//         let substitutions = rule
//             .inference()
//             .free_metavariables()
//             .into_iter()
//             .map(|v| (v.clone(), v.to_formula().to_rwm()))
//             .collect();
//         ProvenInferenceInner {
//             inference: rule.inference().clone(),
//             derivation: InferenceDerivation::Rule {
//                 rule,
//                 substitutions,
//             },
//         }
//         .into()
//     }
//
//     pub fn premise(premises: Vec<RWMFormula>, which: usize) -> ProvenInference {
//         let conclusion = premises[which].clone();
//         ProvenInferenceInner {
//             inference: Inference::new(premises, conclusion),
//             derivation: InferenceDerivation::Premise(which),
//         }
//         .into()
//     }
//
//     pub fn chain(
//         premises: Vec<RWMFormula>,
//         premise_providers: Vec<ProvenInference>,
//         conclusion_provider: ProvenInference,
//     ) -> Result<ProvenInference, String> {
//         for (p, cp) in zip(&premise_providers, &conclusion_provider.premises) {
//             if p.premises != premises {
//                 return Err("Wrong premises given for chain".to_string());
//             }
//             if p.conclusion.as_raw_with_metavariables() != cp.as_raw_with_metavariables() {
//                 return Err(format!(
//                     "Conclusion of {} doesn't match premise {} of {}",
//                     p, cp, conclusion_provider
//                 ));
//             }
//         }
//         let conclusion = conclusion_provider.conclusion.clone();
//         Ok(ProvenInferenceInner {
//             inference: Inference::new(premises, conclusion),
//             derivation: InferenceDerivation::Chain(premise_providers, conclusion_provider),
//         }
//         .into())
//     }
//
//     pub fn derive_by(
//         deriver_name: &str,
//         premises: &[&RWMFormula],
//         conclusion: &RWMFormula,
//     ) -> Result<ProvenInference, String> {
//         let deriver = get_deriver_by_name(deriver_name);
//         deriver.try_derive(premises, conclusion)
//     }
//
//     pub fn derive_chain(
//         deriver_name: &str,
//         premise_providers: Vec<ProvenInference>,
//         conclusion: &RWMFormula,
//     ) -> Result<ProvenInference, String> {
//         let deriver = get_deriver_by_name(deriver_name);
//         let original_premises = premise_providers[0].premises.clone();
//         let intermediate_premises: Vec<&RWMFormula> =
//             premise_providers.iter().map(|p| &p.conclusion).collect();
//         let conclusion_provider = deriver.try_derive(&intermediate_premises, conclusion)?;
//         Self::chain(original_premises, premise_providers, conclusion_provider)
//     }
//
//     #[live_prop_test(
//         postcondition = "result.premises.is_empty() "  // && result.inference.conclusion == todo!()
//     )]
//     pub fn tuple_equality_form(&self) -> ProvenInference {
//         match &self.derivation {
//             InferenceDerivation::Rule {
//                 rule,
//                 substitutions,
//             } => {
//                 let mut apply_chains_equal = rule.internal_proof();
//                 for argument in rule.argument_order() {
//                     let value = substitutions[argument].clone();
//                     let [a, b] = apply_chains_equal.conclusion.as_eq_sides().unwrap();
//                     apply_chains_equal = ProvenInference::chain(
//                         self.premises.clone(),
//                         vec![apply_chains_equal],
//                         ProvenInference::compatibility_left()
//                             .specialize(&substitutions! {A: a, B: b, C: value}),
//                     )
//                     .unwrap();
//                 }
//                 let [a, b] = apply_chains_equal.conclusion.as_eq_sides().unwrap();
//                 let [c, d] = self.inference.tuple_equality_form().map(|t| t.formula());
//                 let ac = ProvenInference::fold_equivalence(a, c).unwrap();
//                 let bd = ProvenInference::fold_equivalence(b, d).unwrap();
//
//                 ProvenInference::eq_trans_chain(&[ac.flip_conclusion(), apply_chains_equal, bd])
//                     .unwrap()
//             }
//             InferenceDerivation::Premise(_which) => {
//                 let [p, c] = self.inference.tuple_equality_form();
//                 p.internal_extraction(&c).unwrap()
//             }
//             InferenceDerivation::Chain(premise_providers, conclusion_provider) => {
//                 let premise_providers = premise_providers.iter().map(|i| i.tuple_equality_form());
//                 let conclusion_provider = conclusion_provider.tuple_equality_form();
//                 let [p, pc] = self.inference.tuple_equality_form();
//                 let mut result = ProvenInference::eq_refl(&p.formula());
//                 let mut form = p.clone();
//                 for premise_provider in premise_providers {
//                     let (pp, e) = form.extend_with_conclusion(premise_provider).unwrap();
//                     form = pp;
//                     result = ProvenInference::eq_trans_chain(&[result, e]).unwrap();
//                 }
//                 let (_ppc, e) = form.extend_with_conclusion(conclusion_provider).unwrap();
//                 //form = ppc;
//                 result = ProvenInference::eq_trans_chain(&[result, e]).unwrap();
//                 result = p.equivalence_with_substitution(&pc, result).unwrap();
//                 result
//             }
//         }
//     }
//     // pub fn tuple_intro(premises: Vec<RWMFormula>) -> ProvenInference{
//     //     ProvenInference::
//     // }
//
//     pub fn metavariable_to_argument(&self, variable_name: &str) -> ProvenInference {
//         let new = self
//             .inference
//             .metavariables_to_arguments(&[variable_name.to_string()]);
//
//         match &self.derivation {
//             InferenceDerivation::Rule {
//                 rule,
//                 substitutions,
//             } => {
//                 todo((rule, substitutions))
//                 // let internal_rule: ProvenInference = rule.internal_proof();
//                 // internal_rule.internal_specialize(
//                 //     rule.argument_order()
//                 //         .iter()
//                 //         .map(|k| {
//                 //             substitutions[k]
//                 //                 .metavariables_to_arguments(&[variable_name.to_string()])
//                 //         })
//                 //         .collect(),
//                 // )
//             }
//             InferenceDerivation::Premise(which) => {
//                 ProvenInference::premise(new.premises.clone(), *which)
//             }
//             InferenceDerivation::Chain(premise_providers, conclusion_provider) => {
//                 let premise_providers = premise_providers
//                     .iter()
//                     .map(|i| i.metavariable_to_argument(variable_name))
//                     .collect();
//                 let conclusion_provider =
//                     conclusion_provider.metavariable_to_argument(variable_name);
//                 ProvenInference::chain(new.premises.clone(), premise_providers, conclusion_provider)
//                     .unwrap()
//             }
//         }
//     }
//
//     pub fn definition_of_const() -> ProvenInference {
//         Rule::by_name("definition of const").internal_proof()
//     }
//
//     pub fn definition_of_fuse() -> ProvenInference {
//         Rule::by_name("definition of fuse").internal_proof()
//     }
//
//     pub fn compatibility_left() -> ProvenInference {
//         Rule::by_name("substitute in LHS").internal_proof()
//     }
//
//     pub fn compatibility_right() -> ProvenInference {
//         Rule::by_name("substitute in RHS").internal_proof()
//     }
//
//     pub fn eq_refl(f: &RWMFormula) -> ProvenInference {
//         ProvenInference::derive_by("eq_refl", &[], &ic!(f = f).to_rwm()).unwrap()
//     }
//
//     pub fn flip_conclusion(&self) -> ProvenInference {
//         let [a, b] = self.conclusion.as_eq_sides().unwrap();
//         ProvenInference::chain(
//             self.premises.clone(),
//             vec![self.clone()],
//             Rule::by_name("symmetry")
//                 .internal_proof()
//                 .specialize(&substitutions! {A: a, B: b}),
//         )
//         .unwrap()
//     }
//
//     pub fn eq_trans_chain(components: &[ProvenInference]) -> Result<ProvenInference, String> {
//         let (first, rest) = components
//             .split_first()
//             .ok_or_else(|| "eq_trans_chain must have at least 1 element".to_string())?;
//         let mut result = first.clone();
//         for inference in rest {
//             if inference.premises != result.premises {
//                 return Err(format!(
//                     "eq_trans_chain components have different premises: `{}`, `{}`",
//                     result, inference
//                 ));
//             }
//             let [a, b1] = result.conclusion.as_eq_sides().unwrap();
//             let [b2, c] = inference.conclusion.as_eq_sides().unwrap();
//
//             if b1 != b2 {
//                 return Err(format!(
//                     "eq_trans_chain components have mismatched conclusions: `{}` vs `{}`",
//                     result.conclusion, inference.conclusion
//                 ));
//             }
//             result = ProvenInference::chain(
//                 result.premises.clone(),
//                 vec![result, inference.clone()],
//                 Rule::by_name("transitivity")
//                     .internal_proof()
//                     .specialize(&substitutions! {A: a, B: b1, C: c}),
//             )
//             .unwrap();
//         }
//         Ok(result)
//     }
//
//     pub fn substitute_whole_formula() -> ProvenInference {
//         todo!()
//     }
// }
pub fn load_proof(path: impl AsRef<Path>) -> Result<Vec<ProofLine>, anyhow::Error> {
    let parser = ProofLineParser::new();
    BufReader::new(File::open(path)?)
        .lines()
        .filter_map(|l| match l {
            Ok(l) => (!l.chars().all(char::is_whitespace) && !l.starts_with('#')).then(|| {
                parser
                    .parse(&l)
                    .map_err(|e| anyhow!(e.to_string()))
                    .and_then(|l| match l.formula {
                        FormulaOrImplicitEquality::Formula(f)
                            if f.to_rwm().as_eq_sides().is_none() =>
                        {
                            Err(anyhow!("Not a proposition: {}", f))
                        }
                        _ => Ok(l),
                    })
                    .map_err(|e| anyhow!("Error while parsing proof line `{l}`: {e}"))
            }),
            Err(e) => Some(Err(e.into())),
        })
        .collect()
}
pub struct ProofScript {
    pub premises: Vec<Formula>,
    pub conclusions: Vec<Formula>,
}

impl ProofScript {
    pub fn new(lines: &[ProofLine]) -> Result<ProofScript, String> {
        // inferences from the premises to that specific conclusion
        let mut premises = Vec::new();
        let mut conclusions = Vec::new();
        let mut previous = Formula::default();
        let mut chain_start = Formula::default();

        for line in lines {
            match line.name.chars().next().unwrap() {
                'P' => {
                    let FormulaOrImplicitEquality::Formula(f) = &line.formula else {
                        return Err(format!(
                            "Premise {} has to be a regular formula but was `{:?}`",
                            line.name, line.formula
                        ));
                    };
                    premises.push(f.clone());
                }
                _ => {
                    match &line.formula {
                        FormulaOrImplicitEquality::Formula(f) => conclusions.push(f.clone()),
                        FormulaOrImplicitEquality::ImplicitEquality(f) => {
                            // let [_l, r] = previous.as_eq_sides().ok_or_else(|| {
                            //     format!(
                            //         "implicit equality `{}. = {}` must follow a proposition",
                            //         line.name, f
                            //     )
                            // })?;
                            conclusions.push(ic!(previous = f));
                            if previous != chain_start {
                                conclusions.push(ic!(chain_start = f));
                            }
                            previous = f.clone();
                        }
                        FormulaOrImplicitEquality::StartEqChain(f) => {
                            previous = f.clone();
                            chain_start = f.clone();
                            continue;
                        }
                    }
                }
            };
        }
        Ok(ProofScript {
            premises,
            conclusions,
        })
    }
}
//
// pub trait Deriver: Send + Sync {
//     fn try_derive(
//         &self,
//         premises: &[&RWMFormula],
//         conclusion: &RWMFormula,
//     ) -> Result<ProvenInference, String>;
// }
//
// pub struct DeriveBySpecializing(pub ProvenInference);
//
// impl Deriver for DeriveBySpecializing {
//     fn try_derive(
//         &self,
//         premises: &[&RWMFormula],
//         conclusion: &RWMFormula,
//     ) -> Result<ProvenInference, String> {
//         let inference = &self.0;
//         let mut arguments: Substitutions = Substitutions::new();
//         inference
//             .conclusion
//             .add_substitutions_to_become(conclusion, &mut arguments)
//             .map_err(|e| {
//                 format!("Could not unify goal `{conclusion}` with conclusion of `{inference}`: {e}")
//             })?;
//         if premises.len() != inference.premises.len() {
//             return Err(format!(
//                 "Wrong number of premises given for inference `{inference}` (given {}, needs {})",
//                 premises.len(),
//                 inference.premises.len()
//             ));
//         }
//         for (needed, &provided) in zip(&inference.premises, premises) {
//             needed.add_substitutions_to_become(provided, &mut arguments).map_err(|e| {
//                 format!(
//                     "Could not unify provided premise `{provided}` with premise `{needed}` of `{inference}`: {e}",
//                 )
//             })?;
//         }
//         Ok(inference.specialize(&arguments))
//     }
// }
//
// pub struct DeriveByAnySingleRule;
//
// impl Deriver for DeriveByAnySingleRule {
//     fn try_derive(
//         &self,
//         premises: &[&RWMFormula],
//         conclusion: &RWMFormula,
//     ) -> Result<ProvenInference, String> {
//         SINGLE_RULE_DERIVERS
//             .iter()
//             .find_map(|(_name, deriver)| deriver.try_derive(premises, conclusion).ok())
//             .ok_or_else(|| format!("No single rule satisfied goal `{}`", &conclusion))
//     }
// }
//
// // pub static ALL_SINGLE_RULES: LazyLock<[(&'static str, ProvenInference); 5]> = LazyLock::new(|| {
// //     [
// //         (
// //             "substitute_whole_formula",
// //             ProvenInference::substitute_whole_formula(),
// //         ),
// //         (
// //             "definition_of_const",
// //             ProvenInference::definition_of_const(),
// //         ),
// //         ("definition_of_fuse", ProvenInference::definition_of_fuse()),
// //         ("compatibility_left", ProvenInference::compatibility_left()),
// //         (
// //             "compatibility_right",
// //             ProvenInference::compatibility_right(),
// //         ),
// //     ]
// // });
//
// static SINGLE_RULE_DERIVERS: LazyLock<Vec<(String, Arc<dyn Deriver>)>> = LazyLock::new(|| {
//     RULES
//         .iter()
//         .map(|(name, rule)| {
//             (
//                 name.clone(),
//                 Arc::new(DeriveBySpecializing(rule.internal_proof())) as Arc<dyn Deriver>,
//             )
//         })
//         .collect()
// });
//
// thread_local! {
//     static ALL_DERIVERS: std::cell::RefCell<HashMap<String, Arc<dyn Deriver>>> = std::cell::RefCell::new(SINGLE_RULE_DERIVERS.iter().map(|(name, deriver)| (name.to_string(), deriver.clone())).collect());
// }
//
// pub fn get_deriver_by_name(name: &str) -> Arc<dyn Deriver> {
//     ALL_DERIVERS.with(|p| {
//         if let Some(existing) = p.borrow().get(name) {
//             return existing.clone();
//         }
//         let compiled = Arc::new(DeriveBySpecializing(
//             compile(&load_proof(Path::new("./data/ic_proofs").join(name)).unwrap())
//                 .map_err(|e| format!("When compiling proof `{name}`, got error: {e}"))
//                 .unwrap(),
//         ));
//
//         p.borrow_mut().insert(name.to_string(), compiled.clone());
//         compiled
//     })
// }
