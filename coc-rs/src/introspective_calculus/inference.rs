use crate::ic;
use crate::introspective_calculus::logic::TrueFormula;
use crate::introspective_calculus::ProofLineParser;
use crate::introspective_calculus::{Formula, FormulaRawness};
use arrayvec::ArrayVec;
use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::iter::zip;
use std::path::Path;
use std::sync::{Arc, LazyLock};

#[derive(Default)]
pub struct ProofLine {
    pub name: String,
    pub formula: Formula,
    pub referents: ArrayVec<String, 2>,
    pub deriver_name: Option<String>,
}

// pub enum CompiledProofStep {
//     Premise(Formula),
//     Axiom(Formula),
//     Lemma {
//         lemma_name: String,
//         arguments: HashMap<String, Formula>,
//         premises: Vec<usize>,
//     },
// }
//
// pub struct CompiledProof {
//     conclusion: Formula,
//     steps: Vec<CompiledProofStep>,
// }

// everything in the same derivation tree is using the same metavariable identities
pub enum SingleRuleInference {
    SubstituteWholeFormula([Formula; 2]),
    DefinitionOfConst([Formula; 2]),
    DefinitionOfFuse([Formula; 3]),
    CompatibilityLeft([Formula; 3]),
    CompatibilityRight([Formula; 3]),
}
pub enum InferenceDerivation {
    Premise(usize),
    Axiom(Formula),
    SingleRule(SingleRuleInference),
    Chain(Vec<Arc<Inference>>, Arc<Inference>),
}

pub struct Inference {
    premises: Vec<Formula>,
    conclusion: Formula,
    derivation: InferenceDerivation,
}

impl Display for Inference {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some((last, rest)) = self.premises.split_last() {
            for premise in rest {
                premise.fmt(f)?;
                ", ".fmt(f)?;
            }
            last.fmt(f)?;
        }
        write!(f, "|- {}", self.conclusion)
    }
}

impl SingleRuleInference {
    fn specialize(&self, arguments: &HashMap<String, Formula>) -> SingleRuleInference {
        use SingleRuleInference::*;
        match self {
            SubstituteWholeFormula(a2) => SubstituteWholeFormula(
                a2.each_ref()
                    .map(|a2| a2.with_metavariables_replaced(arguments)),
            ),
            DefinitionOfConst(a2) => DefinitionOfConst(
                a2.each_ref()
                    .map(|a2| a2.with_metavariables_replaced(arguments)),
            ),
            DefinitionOfFuse(a2) => DefinitionOfFuse(
                a2.each_ref()
                    .map(|a2| a2.with_metavariables_replaced(arguments)),
            ),
            CompatibilityLeft(a2) => CompatibilityLeft(
                a2.each_ref()
                    .map(|a2| a2.with_metavariables_replaced(arguments)),
            ),
            CompatibilityRight(a2) => CompatibilityRight(
                a2.each_ref()
                    .map(|a2| a2.with_metavariables_replaced(arguments)),
            ),
        }
    }
    fn apply(&self, premises: &[&TrueFormula]) -> Result<TrueFormula, String> {
        use SingleRuleInference::*;
        match self {
            SubstituteWholeFormula([_a, _b]) => {
                // if premises[0].formula() != ic!(a = b) {
                //     return Err(format!("Provided premise {} didn't match required premise {a_equals_b} of SubstituteWholeFormula", premises[0].formula()))
                // }
                // if premises[1].formula() != a {
                //     return Err(format!("Provided premise {} didn't match required premise {a_equals_b} of SubstituteWholeFormula", premises[0].formula()))
                // }
                Ok(TrueFormula::substitute_whole_formula(premises[0], premises[1]).unwrap())
            }
            DefinitionOfConst([a, b]) => Ok(TrueFormula::definition_of_const(a.clone(), b.clone())),
            DefinitionOfFuse([a, b, c]) => Ok(TrueFormula::definition_of_fuse(
                a.clone(),
                b.clone(),
                c.clone(),
            )),
            CompatibilityLeft([_a, _b, c]) => {
                Ok(TrueFormula::compatibility_left(premises[0], c.clone()).unwrap())
            }
            CompatibilityRight([_a, _b, c]) => {
                Ok(TrueFormula::compatibility_right(c.clone(), premises[0]).unwrap())
            }
        }
    }
}

impl Inference {
    pub fn specialize(&self, arguments: &HashMap<String, Formula>) -> Inference {
        Inference {
            premises: self
                .premises
                .iter()
                .map(|p| p.with_metavariables_replaced(arguments))
                .collect(),
            conclusion: self.conclusion.with_metavariables_replaced(arguments),
            derivation: match &self.derivation {
                InferenceDerivation::Premise(which) => InferenceDerivation::Premise(*which),
                InferenceDerivation::Axiom(axiom) => InferenceDerivation::Axiom(axiom.clone()),
                InferenceDerivation::SingleRule(rule) => {
                    InferenceDerivation::SingleRule(rule.specialize(arguments))
                }
                InferenceDerivation::Chain(premise_providers, conclusion_provider) => {
                    InferenceDerivation::Chain(
                        premise_providers
                            .iter()
                            .map(|p| Arc::new(p.specialize(arguments)))
                            .collect(),
                        Arc::new(conclusion_provider.specialize(arguments)),
                    )
                }
            },
        }
    }
    pub fn apply(&self, premises: &[&TrueFormula]) -> Result<TrueFormula, String> {
        if premises.len() != self.premises.len() {
            return Err(format!(
                "Wrong number of premises given for inference `{self}` (given {}, needs {})",
                premises.len(),
                self.premises.len()
            ));
        }
        for (required, provided) in zip(&self.premises, premises) {
            if provided.formula() != required {
                return Err(format!(
                    "provided premise {} did not match the required premise {}",
                    provided.formula(),
                    required
                ));
            }
        }
        match &self.derivation {
            InferenceDerivation::Premise(which) => Ok(premises[*which].clone()),
            InferenceDerivation::Axiom(axiom) => Ok(TrueFormula::axiom(axiom.clone())),
            InferenceDerivation::SingleRule(rule) => Ok(rule.apply(premises).unwrap()),
            InferenceDerivation::Chain(premise_providers, conclusion_provider) => {
                let intermediate_premises: Vec<TrueFormula> = premise_providers
                    .iter()
                    .map(|p| p.apply(premises).unwrap())
                    .collect();
                Ok(conclusion_provider
                    .apply(&intermediate_premises.iter().collect_vec())
                    .unwrap())
            }
        }
    }

    pub fn substitute_whole_formula() -> Inference {
        Inference {
            premises: vec![ic!("A" = "B"), ic!("A")],
            conclusion: ic!("B"),
            derivation: InferenceDerivation::SingleRule(
                SingleRuleInference::SubstituteWholeFormula([ic!("A"), ic!("B")]),
            ),
        }
    }

    pub fn definition_of_const() -> Inference {
        Inference {
            premises: vec![],
            conclusion: ic!(((const "A") "B") = "A"),
            derivation: InferenceDerivation::SingleRule(SingleRuleInference::DefinitionOfConst([
                ic!("A"),
                ic!("B"),
            ])),
        }
    }

    pub fn definition_of_fuse() -> Inference {
        Inference {
            premises: vec![],
            conclusion: ic!((((fuse "A") "B") "C") = (("A" "C") ("B" "C"))),
            derivation: InferenceDerivation::SingleRule(SingleRuleInference::DefinitionOfFuse([
                ic!("A"),
                ic!("B"),
                ic!("C"),
            ])),
        }
    }

    pub fn compatibility_left() -> Inference {
        Inference {
            premises: vec![ic!("A" = "B")],
            conclusion: ic!(("A" "C") = ("B" "C")),
            derivation: InferenceDerivation::SingleRule(SingleRuleInference::CompatibilityLeft([
                ic!("A"),
                ic!("B"),
                ic!("C"),
            ])),
        }
    }

    pub fn compatibility_right() -> Inference {
        Inference {
            premises: vec![ic!("A" = "B")],
            conclusion: ic!(("C" "A") = ("C" "B")),
            derivation: InferenceDerivation::SingleRule(SingleRuleInference::CompatibilityRight([
                ic!("A"),
                ic!("B"),
                ic!("C"),
            ])),
        }
    }

    pub fn axiom(premises: Vec<Formula>, axiom: Formula) -> Inference {
        assert_eq!(
            axiom.as_raw_with_metavariables().rawness,
            FormulaRawness::Raw
        );
        Inference {
            premises,
            conclusion: axiom.clone(),
            derivation: InferenceDerivation::Axiom(axiom),
        }
    }

    pub fn premise(premises: Vec<Formula>, which: usize) -> Inference {
        let conclusion = premises[which].clone();
        Inference {
            premises,
            conclusion,
            derivation: InferenceDerivation::Premise(which),
        }
    }

    pub fn chain(
        premises: Vec<Formula>,
        premise_providers: Vec<Arc<Inference>>,
        conclusion_provider: Arc<Inference>,
    ) -> Result<Inference, String> {
        for (p, cp) in zip(&premise_providers, &conclusion_provider.premises) {
            if p.premises != premises {
                return Err("Wrong premises given for chain".to_string());
            }
            if p.conclusion.as_raw_with_metavariables() != cp.as_raw_with_metavariables() {
                return Err(format!(
                    "Conclusion of {} doesn't match premise {} of {}",
                    p, cp, conclusion_provider
                ));
            }
        }
        Ok(Inference {
            premises,
            conclusion: conclusion_provider.conclusion.clone(),
            derivation: InferenceDerivation::Chain(premise_providers, conclusion_provider),
        })
    }
}
pub fn load_proof(path: impl AsRef<Path>) -> Vec<ProofLine> {
    let parser = ProofLineParser::new();
    BufReader::new(File::open(path).unwrap())
        .lines()
        .map(Result::unwrap)
        .filter(|l| !l.chars().all(char::is_whitespace) && !l.starts_with('#'))
        .map(|l| match parser.parse(&l) {
            Ok(a) => a,
            Err(e) => panic!("Got error `{e}` while parsing proof line `{l}`"),
        })
        .collect()
}
pub fn compile(lines: &[ProofLine]) -> Result<Arc<Inference>, String> {
    // inferences from the premises to that specific conclusion
    let mut inferences_by_name: HashMap<&str, Arc<Inference>> = HashMap::with_capacity(lines.len());
    let mut last_inference = None;
    let premises: Vec<Formula> = lines
        .iter()
        .filter(|line| line.name.starts_with('P'))
        .map(|line| line.formula.clone())
        .collect();
    let mut which_premise = 0;
    for line in lines {
        let inference = match line.name.chars().next().unwrap() {
            'A' => Arc::new(Inference::axiom(premises.clone(), line.formula.clone())),
            'P' => {
                let result = Arc::new(Inference::premise(premises.clone(), which_premise));
                which_premise += 1;
                result
            }
            _ => {
                let available_premise_inferences: Vec<Arc<Inference>> = line
                    .referents
                    .iter()
                    .map(|referent_name| inferences_by_name.get(&**referent_name).unwrap().clone())
                    .collect();
                let available_premises: Vec<&Formula> = available_premise_inferences
                    .iter()
                    .map(|p| &p.conclusion)
                    .collect();
                let deriver = line
                    .deriver_name
                    .as_deref()
                    .map(get_deriver_by_name)
                    .unwrap_or_else(|| Arc::new(DeriveByAnySingleRule));
                let here_inference = deriver
                    .try_derive(&available_premises, &line.formula)
                    .map_err(|e| format!("In line {}: {e}", line.name))?;
                Arc::new(Inference::chain(
                    premises.clone(),
                    available_premise_inferences,
                    Arc::new(here_inference),
                )?)
            }
        };
        inferences_by_name.insert(&*line.name, inference.clone());
        last_inference = Some(inference);
    }
    last_inference.ok_or_else(|| "Proof has no lines".to_string())
}

pub trait Deriver: Send + Sync {
    fn try_derive(&self, premises: &[&Formula], conclusion: &Formula) -> Result<Inference, String>;
}

pub struct DeriveBySpecializing(pub Arc<Inference>);

impl Deriver for DeriveBySpecializing {
    fn try_derive(&self, premises: &[&Formula], conclusion: &Formula) -> Result<Inference, String> {
        let inference = &self.0;
        let mut arguments: HashMap<String, Formula> = HashMap::new();
        inference
            .conclusion
            .add_substitutions_to_become(conclusion, &mut arguments)
            .map_err(|e| {
                format!("Could not unify goal `{conclusion}` with conclusion of `{inference}`: {e}")
            })?;
        if premises.len() != inference.premises.len() {
            return Err(format!(
                "Wrong number of premises given for inference `{inference}` (given {}, needs {})",
                premises.len(),
                inference.premises.len()
            ));
        }
        for (needed, &provided) in zip(&inference.premises, premises) {
            needed.add_substitutions_to_become(provided, &mut arguments).map_err(|e| {
                format!(
                    "Could not unify provided premise `{provided}` with premise `{needed}` of `{inference}`: {e}",
                )
            })?;
        }
        Ok(inference.specialize(&arguments))
    }
}

pub struct DeriveByAnySingleRule;

impl Deriver for DeriveByAnySingleRule {
    fn try_derive(&self, premises: &[&Formula], conclusion: &Formula) -> Result<Inference, String> {
        SINGLE_RULE_DERIVERS
            .iter()
            .find_map(|(_name, deriver)| deriver.try_derive(premises, conclusion).ok())
            .ok_or_else(|| format!("No single rule satisfied goal `{}`", &conclusion))
    }
}

static SINGLE_RULE_DERIVERS: LazyLock<[(&'static str, Arc<dyn Deriver>); 5]> =
    LazyLock::new(|| {
        [
            (
                "substitute_whole_formula",
                Arc::new(DeriveBySpecializing(Arc::new(
                    Inference::substitute_whole_formula(),
                ))),
            ),
            (
                "definition_of_const",
                Arc::new(DeriveBySpecializing(Arc::new(
                    Inference::definition_of_const(),
                ))),
            ),
            (
                "definition_of_fuse",
                Arc::new(DeriveBySpecializing(Arc::new(
                    Inference::definition_of_fuse(),
                ))),
            ),
            (
                "compatibility_left",
                Arc::new(DeriveBySpecializing(Arc::new(
                    Inference::compatibility_left(),
                ))),
            ),
            (
                "compatibility_right",
                Arc::new(DeriveBySpecializing(Arc::new(
                    Inference::compatibility_right(),
                ))),
            ),
        ]
    });

thread_local! {
    static ALL_DERIVERS: std::cell::RefCell<HashMap<String, Arc<dyn Deriver>>> = std::cell::RefCell::new(SINGLE_RULE_DERIVERS.iter().map(|(name, deriver)| (name.to_string(), deriver.clone())).collect());
}

pub fn get_deriver_by_name(name: &str) -> Arc<dyn Deriver> {
    ALL_DERIVERS.with(|p| {
        if let Some(existing) = p.borrow().get(name) {
            return existing.clone();
        }
        let compiled = Arc::new(DeriveBySpecializing(
            compile(&load_proof(Path::new("./data/ic_proofs").join(name)))
                .map_err(|e| format!("When compiling proof `{name}`, got error: {e}"))
                .unwrap(),
        ));

        p.borrow_mut().insert(name.to_string(), compiled.clone());
        compiled
    })
}
