use crate::introspective_calculus::derivers::by_specializing_a_proven_inference::DeriveBySpecializing;
use crate::introspective_calculus::inference::{
    proof_premises, Inference, ProofLine, ALL_SINGLE_RULES,
};
use crate::introspective_calculus::Formula;

pub mod by_specializing_a_proven_inference;

#[derive(Debug)]
pub enum IncrementalDeriverWorkResult {
    NothingToDoRightNow,
    StillWorking,
    DiscoveredInference(Inference),
}

pub trait IncrementalDeriver: Send + Sync {
    // fn new(premises: Vec<Formula>) -> Self;
    fn add_goal(&mut self, goal: Formula);
    fn goal_got_proven(&mut self, proof: Inference);
    fn do_some_work(&mut self) -> IncrementalDeriverWorkResult;
}

pub struct TrackedDeriver {
    deriver: Box<dyn IncrementalDeriver>,
    runs: usize,
}

pub struct SearchFromPremisesEnvironment {
    premises: Vec<Formula>,
    goals: Vec<Formula>,
    derivers: Vec<TrackedDeriver>,
}

impl SearchFromPremisesEnvironment {
    pub fn new(premises: Vec<Formula>) -> SearchFromPremisesEnvironment {
        SearchFromPremisesEnvironment {
            premises,
            goals: vec![],
            derivers: vec![],
        }
    }
    pub fn add_goal(&mut self, goal: Formula) {
        for deriver in &mut self.derivers {
            deriver.deriver.add_goal(goal.clone());
        }
        self.goals.push(goal);
    }
    pub fn add_deriver(&mut self, mut deriver: Box<dyn IncrementalDeriver>) {
        for goal in &self.goals {
            deriver.add_goal(goal.clone())
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
impl SearchManyEnvironment {
    pub fn new() -> SearchManyEnvironment {
        SearchManyEnvironment {
            searches: Vec::new(),
        }
    }
    pub fn add_written_proof(&mut self, proof: &[ProofLine]) {
        let premises = proof_premises(proof);
        let mut environment = SearchFromPremisesEnvironment::new(premises.clone());
        for line in proof {
            match line.name.chars().next().unwrap() {
                'P' => {}
                'A' => {}
                _ => environment.add_goal(line.formula.clone()),
            }
        }
        for (_name, inference) in &*ALL_SINGLE_RULES {
            environment.add_deriver(Box::new(DeriveBySpecializing::new(
                inference.clone(),
                premises.clone(),
            )))
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
                    if inference.conclusion() == &search.conclusion {
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
