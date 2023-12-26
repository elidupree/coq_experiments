use crate::introspective_calculus::proof_hierarchy::Proof;
use crate::introspective_calculus::solver_pool::{Goal, SolverPoolInner, SolverWorker};
use crate::introspective_calculus::Substitutions;
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
        // note: only try proofs that are already true from the goal's premises
        let Some(proof_to_specialize) = truths.proven_ucfes.get(self.already_tried_all_before)
        else {
            return WorkResult::Idle;
        };
        self.already_tried_all_before += 1;

        if let Ok(args) = proof_to_specialize.args_to_return(&self.goal.conclusion) {
            return WorkResult::ProducedOutput(proof_to_specialize.specialize(&args));
        }

        WorkResult::StillWorking
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
