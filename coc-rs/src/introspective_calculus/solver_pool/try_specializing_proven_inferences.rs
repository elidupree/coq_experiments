use crate::introspective_calculus::proof_hierarchy::Proof;
use crate::introspective_calculus::solver_pool::{Goal, SolverPoolInner, SolverWorker};
use crate::introspective_calculus::Substitutions;
use ai_framework::time_sharing;
use ai_framework::time_sharing::{TimeSharerKeyless, WorkResult};
use std::collections::HashMap;

struct GoalWorker {
    goal: Goal,
    already_tried_all_before: usize,
}

impl time_sharing::Worker for GoalWorker {
    type Key = usize;
    type Workpiece = SolverPoolInner;
    type Output = Proof;

    fn do_some_work(
        &mut self,
        pool: &mut Self::Workpiece,
        context: &mut time_sharing::WorkContext,
    ) -> WorkResult<Self::Output> {
        // let Some (truths) = pool.truths.by_premises.get(&self.goal.premises) else {return WorkResult::Idle};
        // if self.already_tried_all_before >= pool.truths.proofs.len() {
        //     return WorkResult::Idle
        // }

        if pool.get_goal(&self.goal).is_none() {
            context.completely_done();
            return WorkResult::Idle;
        }

        let truths = pool.truths.by_premises.get(&self.goal.premises).unwrap();
        // note: include proofs that with different premises than the goal's, because we'll specialize them
        let Some(proof_to_specialize) = pool.truths.proofs.get(self.already_tried_all_before)
        else {
            return WorkResult::Idle;
        };
        self.already_tried_all_before += 1;

        let Ok(conclusion_substitutions) = proof_to_specialize
            .conclusion()
            .substitutions_to_become(&self.goal.conclusion)
        else {
            return WorkResult::StillWorking;
        };

        let mut possible_substitutions: HashMap<Substitutions, Vec<Proof>> =
            [(conclusion_substitutions, vec![])].into_iter().collect();
        for premise in proof_to_specialize.premises() {
            possible_substitutions = possible_substitutions
                .into_iter()
                .flat_map(move |(substitutions, premise_providers)| {
                    truths.proofs.iter().filter_map(move |truth| {
                        let mut substitutions = substitutions.clone();
                        let mut premise_providers = premise_providers.clone();
                        premise
                            .add_substitutions_to_become(&truth.conclusion(), &mut substitutions)
                            .ok()?;
                        premise_providers.push(truth.clone());
                        Some((substitutions, premise_providers))
                    })
                })
                .collect();
            if possible_substitutions.is_empty() {
                return WorkResult::StillWorking;
            }
        }

        let (substitutions, premise_providers) = possible_substitutions.into_iter().next().unwrap();
        let result = proof_to_specialize
            .specialize(&substitutions)
            .satisfy_premises_with(&premise_providers);
        assert!(result.premises().is_subset(&self.goal.premises));
        assert_eq!(result.conclusion(), self.goal.conclusion);
        WorkResult::ProducedOutput(result)
    }
}

#[derive(Default)]
pub struct Worker {
    goal_workers: TimeSharerKeyless<GoalWorker>,
}

impl SolverWorker for Worker {
    fn do_some_work(&mut self, pool: &mut SolverPoolInner) -> WorkResult<Proof> {
        self.goal_workers.do_some_work(pool)
    }

    fn goal_added(&mut self, goal: Goal) {
        self.goal_workers.add_worker(GoalWorker {
            goal,
            already_tried_all_before: 0,
        })
    }

    fn proof_discovered(&mut self, _proof: Proof) {
        self.goal_workers.wake_all()
    }
}
