use crate::introspective_calculus::proof_hierarchy::Proof;
use crate::introspective_calculus::solver_pool::{Goal, SolverPoolInner, SolverWorker};
use ai_framework::time_sharing;
use ai_framework::time_sharing::{TimeSharerKeyless, WorkResult};

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

        let mut possible_substitutions = vec![conclusion_substitutions];
        for premise in proof_to_specialize.premises() {
            possible_substitutions = possible_substitutions
                .into_iter()
                .flat_map(move |possible_substitutions| {
                    truths.proofs.iter().filter_map(move |truth| {
                        let mut result = possible_substitutions.clone();
                        premise
                            .add_substitutions_to_become(&truth.conclusion(), &mut result)
                            .ok()?;
                        Some(result)
                    })
                })
                .collect();
            if possible_substitutions.is_empty() {
                return WorkResult::StillWorking;
            }
        }

        WorkResult::ProducedOutput(
            proof_to_specialize.specialize(&possible_substitutions.pop().unwrap()),
        )
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

    fn new_transitive_equality_discovered(&mut self) {
        self.goal_workers.wake_all()
    }
}
