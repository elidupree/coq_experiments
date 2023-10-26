use crate::ic;
use crate::introspective_calculus::logic::TrueFormula;
use crate::introspective_calculus::Formula;
use crate::introspective_calculus::ProofLineParser;
use arrayvec::ArrayVec;
use std::collections::HashMap;
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
    pub lemma_name: Option<String>,
}

pub enum CompiledProofStep {
    Premise(Formula),
    Axiom(Formula),
    Lemma {
        lemma_name: String,
        arguments: HashMap<String, Formula>,
        premises: Vec<usize>,
    },
}

pub struct CompiledProof {
    conclusion: Formula,
    steps: Vec<CompiledProofStep>,
}

pub struct Claim {
    premises: Vec<Formula>,
    conclusion: Formula,
}

pub fn load_proof(path: impl AsRef<Path>) -> Vec<ProofLine> {
    let parser = ProofLineParser::new();
    BufReader::new(File::open(path).unwrap())
        .lines()
        .map(Result::unwrap)
        .filter(|l| !l.chars().all(char::is_whitespace) && !l.starts_with("#"))
        .map(|l| match parser.parse(&l) {
            Ok(a) => a,
            Err(e) => panic!("Got error `{e}` while parsing proof line `{l}`"),
        })
        .collect()
}
pub fn lemma_step(
    lemma_name: &str,
    goal: &Formula,
    provided_premises: &[(usize, &Formula)],
) -> Result<CompiledProofStep, String> {
    let lemma = get_proof_by_name(lemma_name);
    let claim = lemma.claim();
    eprintln!("{} -> {goal}", &claim.conclusion);
    let mut arguments: HashMap<String, Formula> = HashMap::new();
    claim
        .conclusion
        .add_substitutions_to_become(goal, &mut arguments)
        .map_err(|e| {
            format!(
                "Could not unify goal `{goal}` with conclusion `{}` of `{lemma_name}`: {e}",
                &claim.conclusion
            )
        })?;
    if provided_premises.len() != claim.premises.len() {
        return Err(format!(
            "Wrong number of premises given for lemma `{lemma_name}` (given {}, needs {})",
            provided_premises.len(),
            claim.premises.len()
        ));
    }
    for (needed, &(_index, provided)) in zip(claim.premises, provided_premises) {
        needed.add_substitutions_to_become(provided, &mut arguments).map_err(|e| {
            format!(
                "Could not unify provided premise `{provided}` with premise `{needed}` of `{lemma_name}`: {e}",
            )
        })?;
    }
    let premises = provided_premises.iter().map(|&(index, _)| index).collect();
    Ok(CompiledProofStep::Lemma {
        lemma_name: lemma_name.to_string(),
        arguments,
        premises,
    })
}
pub fn compile(lines: &[ProofLine]) -> Result<CompiledProof, String> {
    let mut steps = Vec::with_capacity(lines.len());
    let mut positions_by_name = HashMap::with_capacity(lines.len());
    for line in lines {
        positions_by_name.insert(line.name.clone(), steps.len());
        let step = match line.name.chars().next().unwrap() {
            'A' => CompiledProofStep::Axiom(line.formula.clone()),
            'P' => CompiledProofStep::Premise(line.formula.clone()),
            _ => {
                let available_premises: Vec<(usize, &Formula)> = line
                    .referents
                    .iter()
                    .map(|referent_name| {
                        let index = *positions_by_name.get(referent_name).unwrap();
                        let formula = &lines[index].formula;
                        (index, formula)
                    })
                    .collect();
                match &line.lemma_name {
                    Some(lemma_name) => lemma_step(lemma_name, &line.formula, &available_premises)?,
                    None => INHERENT_RULE_PROOFS
                        .iter()
                        .find_map(|(name, _)| {
                            lemma_step(name, &line.formula, &available_premises).ok()
                        })
                        .ok_or_else(|| {
                            format!("No inherent rule satisfied goal `{}`", &line.formula)
                        })?,
                }
            }
        };
        steps.push(step);
    }
    Ok(CompiledProof {
        conclusion: lines
            .last()
            .ok_or_else(|| "Proof has no lines".to_string())?
            .formula
            .clone(),
        steps,
    })
}

static INHERENT_RULE_PROOFS: LazyLock<[(&'static str, Arc<dyn Proof>); 5]> = LazyLock::new(|| {
    [
        ("substitute_whole_formula", Arc::new(SubstituteWholeFormula)),
        ("definition_of_const", Arc::new(DefinitionOfConst)),
        ("definition_of_fuse", Arc::new(DefinitionOfFuse)),
        ("compatibility_left", Arc::new(CompatibilityLeft)),
        ("compatibility_right", Arc::new(CompatibilityRight)),
    ]
});

thread_local! {
    static ALL_PROOFS: std::cell::RefCell<HashMap<String, Arc<dyn Proof>>> = std::cell::RefCell::new(INHERENT_RULE_PROOFS.iter().map(|(name, proof)| (name.to_string(), proof.clone())).collect());
}

pub fn get_proof_by_name(name: &str) -> Arc<dyn Proof> {
    ALL_PROOFS.with(|p| {
        if let Some(existing) = p.borrow().get(name) {
            return existing.clone();
        }
        let compiled = Arc::new(
            compile(&load_proof(Path::new("./data/ic_proofs").join(name)))
                .map_err(|e| format!("When compiling proof `{name}`, got error: {e}"))
                .unwrap(),
        );

        p.borrow_mut().insert(name.to_string(), compiled.clone());
        compiled
    })
}

pub trait Proof: Send + Sync {
    fn claim(&self) -> Claim;
    fn execute(
        &self,
        arguments: &HashMap<String, Formula>,
        premises: &[&TrueFormula],
    ) -> Option<TrueFormula>;
}

pub struct SubstituteWholeFormula;
impl Proof for SubstituteWholeFormula {
    fn claim(&self) -> Claim {
        Claim {
            premises: vec![ic!("A" = "B"), ic!("A")],
            conclusion: ic!("B"),
        }
    }
    fn execute(
        &self,
        _arguments: &HashMap<String, Formula>,
        premises: &[&TrueFormula],
    ) -> Option<TrueFormula> {
        TrueFormula::substitute_whole_formula(premises.get(0)?, premises.get(1)?)
    }
}

pub struct DefinitionOfConst;
impl Proof for DefinitionOfConst {
    fn claim(&self) -> Claim {
        Claim {
            premises: vec![],
            conclusion: ic!(((const "A") "B") = "A"),
        }
    }

    fn execute(
        &self,
        arguments: &HashMap<String, Formula>,
        _premises: &[&TrueFormula],
    ) -> Option<TrueFormula> {
        Some(TrueFormula::definition_of_const(
            arguments.get("A")?.clone(),
            arguments.get("B")?.clone(),
        ))
    }
}

pub struct DefinitionOfFuse;
impl Proof for DefinitionOfFuse {
    fn claim(&self) -> Claim {
        Claim {
            premises: vec![],
            conclusion: ic!((((fuse "A") "B") "C") = (("A" "C") ("B" "C"))),
        }
    }
    fn execute(
        &self,
        arguments: &HashMap<String, Formula>,
        _premises: &[&TrueFormula],
    ) -> Option<TrueFormula> {
        Some(TrueFormula::definition_of_fuse(
            arguments.get("A")?.clone(),
            arguments.get("B")?.clone(),
            arguments.get("C")?.clone(),
        ))
    }
}

pub struct CompatibilityLeft;
impl Proof for CompatibilityLeft {
    fn claim(&self) -> Claim {
        Claim {
            premises: vec![ic!("A" = "B")],
            conclusion: ic!(("A" "C") = ("B" "C")),
        }
    }
    fn execute(
        &self,
        arguments: &HashMap<String, Formula>,
        premises: &[&TrueFormula],
    ) -> Option<TrueFormula> {
        TrueFormula::compatibility_left(premises.get(0)?, arguments.get("C")?.clone())
    }
}

pub struct CompatibilityRight;
impl Proof for CompatibilityRight {
    fn claim(&self) -> Claim {
        Claim {
            premises: vec![ic!("A" = "B")],
            conclusion: ic!(("C" "A") = ("C" "B")),
        }
    }
    fn execute(
        &self,
        arguments: &HashMap<String, Formula>,
        premises: &[&TrueFormula],
    ) -> Option<TrueFormula> {
        TrueFormula::compatibility_right(arguments.get("C")?.clone(), premises.get(0)?)
    }
}

impl Proof for CompiledProof {
    fn claim(&self) -> Claim {
        Claim {
            premises: self
                .steps
                .iter()
                .filter_map(|step| match step {
                    CompiledProofStep::Premise(p) => Some(p.clone()),
                    _ => None,
                })
                .collect(),
            conclusion: self.conclusion.clone(),
        }
    }
    fn execute(
        &self,
        arguments: &HashMap<String, Formula>,
        premises: &[&TrueFormula],
    ) -> Option<TrueFormula> {
        let mut conclusions = Vec::with_capacity(self.steps.len());
        let specialize = |f: &Formula| f.with_metavariables_replaced(arguments);
        let mut premises = premises.iter().copied();
        for step in &self.steps {
            let conclusion = match step {
                CompiledProofStep::Premise(required) => {
                    let p = premises
                        .next()
                        .expect("insufficient premises provided for proof");
                    assert_eq!(p.formula(), required, "wrong premise provided for proof");
                    p.clone()
                }
                CompiledProofStep::Axiom(a) => TrueFormula::axiom(a.clone()),
                CompiledProofStep::Lemma {
                    lemma_name,
                    arguments,
                    premises,
                } => {
                    let lemma = get_proof_by_name(lemma_name);
                    let arguments = arguments
                        .iter()
                        .map(|(name, value)| (name.clone(), specialize(value)))
                        .collect();
                    let premises: Vec<_> = premises.iter().map(|&i| &conclusions[i]).collect();
                    lemma.execute(&arguments, &premises)?
                }
            };
            conclusions.push(conclusion);
        }
        Some(conclusions.pop().unwrap())
    }
}
