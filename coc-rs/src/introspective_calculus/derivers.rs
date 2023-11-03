use crate::introspective_calculus::derivers::by_specializing_a_proven_inference::DeriveBySpecializing;
use crate::introspective_calculus::derivers::by_substitution::DeriveBySubstitution;
use crate::introspective_calculus::inference::{
    proof_axioms, proof_premises, Inference, ProofLine, ALL_SINGLE_RULES,
};
use crate::introspective_calculus::{Formula, RWMFormula, RawFormula};
use std::collections::{HashMap, HashSet};

pub mod by_specializing_a_proven_inference;
pub mod by_substitution;

#[derive(Debug)]
pub enum IncrementalDeriverWorkResult {
    NothingToDoRightNow,
    StillWorking,
    DiscoveredInference(Inference),
}

pub trait IncrementalDeriver: Send + Sync {
    // fn new(premises: Vec<RWMFormula>) -> Self;
    fn add_goal(&mut self, goal: RWMFormula);
    fn goal_got_proven(&mut self, proof: Inference);
    fn do_some_work(&mut self) -> IncrementalDeriverWorkResult;
}

pub struct TrackedDeriver {
    deriver: Box<dyn IncrementalDeriver>,
    runs: usize,
}

pub struct SearchFromPremisesEnvironment {
    premises: Vec<RWMFormula>,
    goals: HashSet<RWMFormula>,
    known_truths: HashMap<RWMFormula, Inference>,
    derivers: Vec<TrackedDeriver>,
}

impl SearchFromPremisesEnvironment {
    pub fn new(
        premises: Vec<RWMFormula>,
        axioms: Vec<RawFormula>,
    ) -> SearchFromPremisesEnvironment {
        let known_truths = premises
            .iter()
            .enumerate()
            .map(|(i, p)| (p.clone(), Inference::premise(premises.clone(), i)))
            .chain(
                axioms
                    .into_iter()
                    .map(|a| (a.to_rwm(), Inference::axiom(premises.clone(), a))),
            )
            .collect();
        SearchFromPremisesEnvironment {
            premises,
            goals: Default::default(),
            known_truths,
            derivers: vec![],
        }
    }
    pub fn add_goal(&mut self, goal: RWMFormula) {
        // println!("adding goal {goal}");
        for deriver in &mut self.derivers {
            deriver.deriver.add_goal(goal.clone());
        }
        self.goals.insert(goal);
    }
    pub fn add_deriver(&mut self, mut deriver: Box<dyn IncrementalDeriver>) {
        for goal in &self.goals {
            deriver.add_goal(goal.clone());
        }
        for inference in self.known_truths.values() {
            deriver.goal_got_proven(inference.clone());
        }
        self.derivers.push(TrackedDeriver { deriver, runs: 0 });
    }
    pub fn do_some_work(&mut self) -> IncrementalDeriverWorkResult {
        if self.derivers.is_empty() {
            return IncrementalDeriverWorkResult::NothingToDoRightNow;
        }
        self.derivers.sort_by_key(|d| d.runs);
        for deriver in &mut self.derivers {
            deriver.runs += 1;
            match deriver.deriver.do_some_work() {
                IncrementalDeriverWorkResult::NothingToDoRightNow => {}
                IncrementalDeriverWorkResult::StillWorking => {
                    return IncrementalDeriverWorkResult::StillWorking
                }
                IncrementalDeriverWorkResult::DiscoveredInference(inference) => {
                    for deriver in &mut self.derivers {
                        deriver.deriver.goal_got_proven(inference.clone());
                    }
                    let existing = self
                        .known_truths
                        .insert(inference.conclusion().clone(), inference.clone());
                    // println!("...discovered {inference}");
                    if existing.is_some() {
                        panic!("discovered {inference}\nwait a minute, that was already known!")
                    }
                    if !self.goals.contains(inference.conclusion()) {
                        eprintln!(
                            "discovered {inference}\nwait a minute, that wasn't a goal! Goals are:"
                        );
                        for goal in &self.goals {
                            eprintln!("> {goal}");
                        }
                        panic!();
                    }

                    return IncrementalDeriverWorkResult::DiscoveredInference(inference);
                }
            }
        }
        IncrementalDeriverWorkResult::NothingToDoRightNow
    }
}

struct SearchForProofOfSpecificInference {
    environment: SearchFromPremisesEnvironment,
    conclusion: Formula,
    runs: usize,
}

pub struct SearchManyEnvironment {
    searches: Vec<SearchForProofOfSpecificInference>,
}
impl Default for SearchManyEnvironment {
    fn default() -> Self {
        Self::new()
    }
}
impl SearchManyEnvironment {
    pub fn new() -> SearchManyEnvironment {
        SearchManyEnvironment {
            searches: Vec::new(),
        }
    }
    pub fn add_written_proof(&mut self, proof: &[ProofLine]) {
        let premises: Vec<RWMFormula> = proof_premises(proof);
        let axioms: Vec<RawFormula> = proof_axioms(proof);
        let mut environment = SearchFromPremisesEnvironment::new(premises.clone(), axioms);
        for (_name, inference) in &*ALL_SINGLE_RULES {
            environment.add_deriver(Box::new(DeriveBySpecializing::new(
                inference.clone(),
                premises.clone(),
            )))
        }
        environment.add_deriver(Box::new(DeriveBySubstitution::new(premises.clone())));
        for line in proof {
            match line.name.chars().next().unwrap() {
                'P' => {}
                'A' => {}
                _ => environment.add_goal(line.formula.to_rwm()),
            }
        }
        self.searches.push(SearchForProofOfSpecificInference {
            environment,
            conclusion: proof.last().unwrap().formula.clone(),
            runs: 0,
        });
    }
    pub fn do_some_work(&mut self) -> IncrementalDeriverWorkResult {
        self.searches.sort_by_key(|d| d.runs);

        for (i, search) in self.searches.iter_mut().enumerate() {
            search.runs += 1;
            match search.environment.do_some_work() {
                IncrementalDeriverWorkResult::NothingToDoRightNow => {}
                IncrementalDeriverWorkResult::StillWorking => {
                    return IncrementalDeriverWorkResult::StillWorking
                }
                IncrementalDeriverWorkResult::DiscoveredInference(inference) => {
                    if inference.conclusion() == &search.conclusion.to_rwm() {
                        self.searches.remove(i);
                        for search in &mut self.searches {
                            search
                                .environment
                                .add_deriver(Box::new(DeriveBySpecializing::new(
                                    inference.clone(),
                                    search.environment.premises.clone(),
                                )))
                        }
                        return IncrementalDeriverWorkResult::DiscoveredInference(inference);
                    }
                    return IncrementalDeriverWorkResult::StillWorking;
                }
            }
        }
        IncrementalDeriverWorkResult::NothingToDoRightNow
    }
}
