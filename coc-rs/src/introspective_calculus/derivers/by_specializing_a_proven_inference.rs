use crate::introspective_calculus::derivers::{IncrementalDeriver, IncrementalDeriverWorkResult};
use crate::introspective_calculus::inference::Inference;
use crate::introspective_calculus::{merge_substitutions_into, Formula};
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone)]
enum WhatSubstitutions {
    NotYetCalculated,
    Unsatisfiable,
    Known(Arc<HashMap<String, Formula>>),
}

struct TruthInfo {
    known_inference: Inference,
    substitutions_for_my_premises_to_become_this_conclusion: Vec<WhatSubstitutions>,
}
struct GoalInfo {
    substitutions_for_my_conclusion_to_become_this_goal: WhatSubstitutions,
    premises_tried: PremisesTried,
}
struct PremisesTried {
    already_tried_every_combination_before: usize,
    next_trial: Vec<usize>,
}
impl PremisesTried {
    fn pick_next_trial(&mut self) -> Vec<usize> {
        let result = self.next_trial.clone();
        for (which_premise, i) in self.next_trial.iter_mut().enumerate() {
            *i += 1;
            if *i <= self.already_tried_every_combination_before {
                break;
            } else {
                *i = 0;
                if which_premise + 1 == result.len() {
                    self.already_tried_every_combination_before += 1;
                }
            }
        }
        // hack - zero case is special
        if result.is_empty() {
            self.already_tried_every_combination_before = usize::MAX;
        } else {
            // auto-skip over the ones tried in previous hypercubes
            if self
                .next_trial
                .iter()
                .all(|&i| i < self.already_tried_every_combination_before)
            {
                *self.next_trial.first_mut().unwrap() = self.already_tried_every_combination_before;
            }
        }
        result
    }
}

impl WhatSubstitutions {
    pub fn get(
        &mut self,
        parametric: &Formula,
        goal: &Formula,
    ) -> Option<Arc<HashMap<String, Formula>>> {
        if let WhatSubstitutions::NotYetCalculated = self {
            *self = match parametric.substitutions_to_become(goal) {
                Ok(substitutions) => WhatSubstitutions::Known(Arc::new(substitutions)),
                Err(_) => WhatSubstitutions::Unsatisfiable,
            };
        }
        if let WhatSubstitutions::Known(substitutions) = self {
            Some(substitutions.clone())
        } else {
            None
        }
    }
}

/// in some sequence, try every choose-p of the known truths with every unsolved goal, and
pub struct DeriveBySpecializing {
    inference_to_specialize: Inference,
    available_premises: Vec<Formula>,
    // inferences starting from the premises
    known_truths: Vec<TruthInfo>,
    unsolved_goals: HashMap<Formula, GoalInfo>,
}

impl DeriveBySpecializing {
    pub fn new(
        inference_to_specialize: Inference,
        available_premises: Vec<Formula>,
    ) -> DeriveBySpecializing {
        let known_truths = available_premises
            .iter()
            .enumerate()
            .map(|(i, _p)| TruthInfo {
                known_inference: Inference::premise(available_premises.clone(), i),
                substitutions_for_my_premises_to_become_this_conclusion: vec![
                        WhatSubstitutions::NotYetCalculated;
                        inference_to_specialize.premises().len()
                    ],
            })
            .collect();
        DeriveBySpecializing {
            inference_to_specialize,
            available_premises,
            known_truths,
            unsolved_goals: HashMap::new(),
        }
    }
}

impl IncrementalDeriver for DeriveBySpecializing {
    fn add_goal(&mut self, goal: Formula) {
        self.unsolved_goals.insert(
            goal,
            GoalInfo {
                substitutions_for_my_conclusion_to_become_this_goal:
                    WhatSubstitutions::NotYetCalculated,
                premises_tried: PremisesTried {
                    already_tried_every_combination_before: 0,
                    next_trial: vec![0; self.inference_to_specialize.premises().len()],
                },
            },
        );
    }

    fn goal_got_proven(&mut self, proof: Inference) {
        self.unsolved_goals.remove(proof.conclusion());
        self.known_truths.push(TruthInfo {
            known_inference: proof,
            substitutions_for_my_premises_to_become_this_conclusion: vec![
                    WhatSubstitutions::NotYetCalculated;
                    self.inference_to_specialize.premises().len()
                ],
        })
    }

    fn do_some_work(&mut self) -> IncrementalDeriverWorkResult {
        for (goal, goal_info) in &mut self.unsolved_goals {
            if let Some(substitutions) = goal_info
                .substitutions_for_my_conclusion_to_become_this_goal
                .get(self.inference_to_specialize.conclusion(), goal)
            {
                if goal_info
                    .premises_tried
                    .already_tried_every_combination_before
                    < self.known_truths.len()
                {
                    let trial = goal_info.premises_tried.pick_next_trial();
                    let mut substitutions = (*substitutions).clone();
                    for (which_premise, &i) in trial.iter().enumerate() {
                        let c = self.known_truths[i].known_inference.conclusion().clone();
                        if let Some(premise_substitutions) = self.known_truths[i]
                            .substitutions_for_my_premises_to_become_this_conclusion[which_premise]
                            .get(&self.inference_to_specialize.premises()[which_premise], &c)
                        {
                            if merge_substitutions_into(&mut substitutions, &premise_substitutions)
                                .is_err()
                            {
                                return IncrementalDeriverWorkResult::StillWorking;
                            }
                        }
                    }

                    let specialized = self.inference_to_specialize.specialize(&substitutions);
                    let full_inference = Inference::chain(
                        self.available_premises.clone(),
                        trial
                            .iter()
                            .map(|&i| self.known_truths[i].known_inference.clone())
                            .collect(),
                        specialized,
                    )
                    .unwrap();

                    return IncrementalDeriverWorkResult::DiscoveredInference(full_inference);
                }
            }
        }
        IncrementalDeriverWorkResult::NothingToDoRightNow
    }
}
