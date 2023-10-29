use crate::introspective_calculus::inference::Inference;
use crate::introspective_calculus::Formula;

pub mod by_specializing_a_proven_inference;

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
    derivers: Vec<TrackedDeriver>,
}

impl SearchFromPremisesEnvironment {
    pub fn new(premises: Vec<Formula>) -> SearchFromPremisesEnvironment {
        SearchFromPremisesEnvironment {
            premises,
            derivers: vec![],
        }
    }
    pub fn add_goal(&mut self, goal: Formula) {
        for deriver in &mut self.derivers {
            deriver.deriver.add_goal(goal.clone());
        }
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
