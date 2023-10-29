use crate::introspective_calculus::inference::Inference;
use crate::introspective_calculus::Formula;

pub mod by_specializing_a_proven_inference;

pub enum IncrementalDeriverWorkResult {
    NothingLeftToDo,
    StillWorking,
    DiscoveredInference(Inference),
}

pub trait IncrementalDeriver {
    // fn new(premises: Vec<Formula>) -> Self;
    fn add_goal(&mut self, goal: Formula);
    fn goal_got_proven(&mut self, proof: Inference);
    fn do_some_work(&mut self) -> IncrementalDeriverWorkResult;
}
