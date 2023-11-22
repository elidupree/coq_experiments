use crate::introspective_calculus::derivers::by_specializing_a_proven_inference::DeriveBySpecializing;
use crate::introspective_calculus::derivers::by_substitution_and_unfolding::DeriveBySubstitutionAndUnfolding;
use crate::introspective_calculus::inference::{ProofLine, ProvenInference};
use crate::introspective_calculus::rules::RULES;
use crate::introspective_calculus::{Formula, RWMFormula, RawFormula};
use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

pub mod by_specializing_a_proven_inference;
pub mod by_substitution_and_unfolding;

#[derive(Debug)]
pub enum IncrementalDeriverWorkResult {
    NothingToDoRightNow,
    StillWorking,
    DiscoveredInference(ProvenInference),
}

pub trait IncrementalDeriver: Send + Sync {
    // fn new(premises: Vec<RWMFormula>) -> Self;
    fn description(&self) -> String;
    fn add_goal(&mut self, goal: RWMFormula);
    fn goal_got_proven(&mut self, proof: ProvenInference);
    fn do_some_work(&mut self) -> IncrementalDeriverWorkResult;
}

pub struct TrackedDeriver {
    deriver: Box<dyn IncrementalDeriver>,
    runs: usize,
}

pub struct SearchFromPremisesEnvironment {
    premises: Vec<RWMFormula>,
    goals: HashSet<RWMFormula>,
    known_truths: HashMap<RWMFormula, ProvenInference>,
    derivers: Vec<TrackedDeriver>,
}

impl SearchFromPremisesEnvironment {
    pub fn new(
        premises: Vec<RWMFormula>,
        _axioms: Vec<RawFormula>,
    ) -> SearchFromPremisesEnvironment {
        let known_truths = premises
            .iter()
            .enumerate()
            .map(|(i, p)| (p.clone(), ProvenInference::premise(premises.clone(), i)))
            // .chain(
            //     axioms
            //         .into_iter()
            //         .map(|a| (a.to_rwm(), ProvenInference::axiom(premises.clone(), a))),
            // )
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
                    let deriver_description = deriver.deriver.description();
                    let existing = self
                        .known_truths
                        .insert(inference.conclusion.clone(), inference.clone());
                    // println!("...discovered {inference}");
                    let mut problems = Vec::new();
                    if inference.premises != self.premises {
                        problems.push("* That has the wrong premises!".to_string());
                    }
                    if existing.is_some() {
                        problems.push("* That was already known!".to_string());
                    }
                    if !self.goals.contains(&inference.conclusion) {
                        problems.push("* That wasn't a goal!".to_string());
                        format!(
                            "* That wasn't a goal! Goals are:\n{}",
                            self.goals.iter().map(|goal| format!("> {goal}")).join("\n")
                        );
                    }
                    if !problems.is_empty() {
                        let problems = problems.join("\n");
                        panic!(
                            "While working from {}...\n{deriver_description} discovered {inference}\nWait a minute!\n{problems}\n",
                            self.premises.iter().map(ToString::to_string).join(", ")
                        );
                    }

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

struct SearchForProofOfSpecificInference<Line> {
    lines: Vec<Line>,
    environment: SearchFromPremisesEnvironment,
    runs: usize,
}

pub struct SearchManyEnvironment<SearchKey, Line> {
    searches: HashMap<SearchKey, SearchForProofOfSpecificInference<Line>>,
}
impl<SearchKey, Line> Default for SearchManyEnvironment<SearchKey, Line> {
    fn default() -> Self {
        Self::new()
    }
}

pub trait SearchLineTrait {
    fn formula(&self) -> RWMFormula;
    fn is_premise(&self) -> bool;
    fn is_axiom(&self) -> bool;
    fn is_conclusion(&self) -> bool;
    fn proven(&mut self, inference: ProvenInference);
}

pub struct PrettyLine {
    pub name: String,
    pub formula: Formula,
    pub is_premise: bool,
    pub is_axiom: bool,
    pub is_conclusion: bool,
    pub proof: Option<ProvenInference>,
}

impl SearchLineTrait for PrettyLine {
    fn formula(&self) -> RWMFormula {
        self.formula.to_rwm()
    }

    fn is_premise(&self) -> bool {
        self.is_premise
    }

    fn is_axiom(&self) -> bool {
        self.is_axiom
    }

    fn is_conclusion(&self) -> bool {
        self.is_conclusion
    }

    fn proven(&mut self, inference: ProvenInference) {
        self.proof = Some(inference)
    }
}

pub fn pretty_lines(lines: &[ProofLine]) -> Vec<PrettyLine> {
    let mut result: Vec<PrettyLine> = lines
        .iter()
        .map(|line| PrettyLine {
            name: line.name.clone(),
            formula: line.formula.clone(),
            is_premise: line.name.starts_with('P'),
            is_axiom: line.name.starts_with('A'),
            is_conclusion: false,
            proof: None,
        })
        .collect();
    result.last_mut().unwrap().is_conclusion = true;
    result
}

impl<SearchKey, Line> SearchManyEnvironment<SearchKey, Line> {
    pub fn new() -> Self {
        SearchManyEnvironment {
            searches: HashMap::new(),
        }
    }
}
impl<SearchKey: Eq + Hash + Clone, Line: SearchLineTrait> SearchManyEnvironment<SearchKey, Line> {
    pub fn add_search(&mut self, key: SearchKey, lines: Vec<Line>) {
        let premises: Vec<RWMFormula> = lines
            .iter()
            .filter(|l| l.is_premise())
            .map(Line::formula)
            .collect();
        let axioms: Vec<RawFormula> = lines
            .iter()
            .filter(|l| l.is_axiom())
            .map(Line::formula)
            .filter_map(|f| f.to_raw())
            .collect();
        let mut environment = SearchFromPremisesEnvironment::new(premises.clone(), axioms);
        for (_name, rule) in &*RULES {
            environment.add_deriver(Box::new(DeriveBySpecializing::new(
                rule.internal_proof().clone(),
                premises.clone(),
            )))
        }
        environment.add_deriver(Box::new(DeriveBySubstitutionAndUnfolding::new(
            premises.clone(),
        )));
        for line in &lines {
            if !(line.is_premise() || line.is_axiom()) {
                environment.add_goal(line.formula());
            }
        }
        self.searches.insert(
            key,
            SearchForProofOfSpecificInference {
                lines,
                environment,
                runs: 0,
            },
        );
    }

    pub fn do_some_work(&mut self) -> IncrementalDeriverWorkResult {
        //self.searches.sort_by_key(|d| d.runs);

        for (key, search) in self.searches.iter_mut() {
            search.runs += 1;
            match search.environment.do_some_work() {
                IncrementalDeriverWorkResult::NothingToDoRightNow => {}
                IncrementalDeriverWorkResult::StillWorking => {
                    return IncrementalDeriverWorkResult::StillWorking
                }
                IncrementalDeriverWorkResult::DiscoveredInference(inference) => {
                    let mut is_conclusion = false;
                    for line in &mut search.lines {
                        if line.formula() == inference.conclusion {
                            line.proven(inference.clone());
                            if line.is_conclusion() {
                                is_conclusion = true
                            }
                        }
                    }
                    if is_conclusion {
                        if false {
                            let key = key.clone();
                            self.searches.remove(&key);
                        }
                        for search in self.searches.values_mut() {
                            search
                                .environment
                                .add_deriver(Box::new(DeriveBySpecializing::new(
                                    inference.clone(),
                                    search.environment.premises.clone(),
                                )))
                        }
                    }
                    return IncrementalDeriverWorkResult::DiscoveredInference(inference);
                }
            }
        }
        IncrementalDeriverWorkResult::NothingToDoRightNow
    }

    pub fn searches_lines(&self) -> HashMap<&SearchKey, &[Line]> {
        self.searches.iter().map(|(k, v)| (k, &*v.lines)).collect()
    }
}
