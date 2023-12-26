use crate::introspective_calculus::proof_hierarchy::Proof;
use crate::introspective_calculus::solver_pool::{Goal, SolverPoolInner, SolverWorker};
use ai_framework::time_sharing;
use ai_framework::time_sharing::{TimeSharerKeyless, WorkResult};
use itertools::Itertools;
use std::iter::zip;

struct GoalWorker {
    goal: Goal,
    proofs_tried: Vec<PremisesTried>,
    // already_tried_all_before: usize,
    num_premise_candidates_at_last_iteration_start: usize,
    current_proof: usize,
}
struct PremisesTried {
    already_tried_every_combination_before: usize,
    next_trial: Vec<usize>,
}
impl PremisesTried {
    fn failed_hard(&mut self) {
        self.already_tried_every_combination_before = usize::MAX;
    }
    fn failed_at_premise(&mut self, index: usize, num_candidates: usize) {
        assert!(num_candidates > self.already_tried_every_combination_before);
        self.next_trial[index] += 1;
        if self.next_trial[index] >= num_candidates {
            match index.checked_sub(1) {
                None => {
                    self.already_tried_every_combination_before = num_candidates;
                }
                Some(pred) => {
                    self.failed_at_premise(pred, num_candidates);
                }
            }
        } else {
            for entry in &mut self.next_trial[index + 1..] {
                *entry = 0;
            }
            // auto-skip over the ones tried in previous hypercubes
            if self
                .next_trial
                .iter()
                .all(|&i| i < self.already_tried_every_combination_before)
            {
                *self.next_trial.last_mut().unwrap() = self.already_tried_every_combination_before;
            }
        }
    }
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

        let truths_for_my_premises = pool.truths.by_premises.get(&self.goal.premises).unwrap();

        // note: `pool.truths` - include proofs with different premises than the goal's, because we'll specialize them
        let mut proof_to_specialize = pool.truths.important_proofs.get(self.current_proof);
        if proof_to_specialize.is_none() {
            if truths_for_my_premises.important_proofs.len()
                == self.num_premise_candidates_at_last_iteration_start
            {
                return WorkResult::Idle;
            }
            self.num_premise_candidates_at_last_iteration_start =
                truths_for_my_premises.important_proofs.len();
            self.current_proof = 0;
            proof_to_specialize = pool.truths.important_proofs.get(self.current_proof);
        }
        let Some(proof_to_specialize) = proof_to_specialize else {
            return WorkResult::Idle;
        };

        if self.proofs_tried.len() <= self.current_proof {
            self.proofs_tried.push(PremisesTried {
                already_tried_every_combination_before: 0,
                next_trial: vec![0; proof_to_specialize.premises().len()],
            })
        }

        let premises_tried = &mut self.proofs_tried[self.current_proof];

        if premises_tried.already_tried_every_combination_before
            >= self.num_premise_candidates_at_last_iteration_start
        {
            self.current_proof += 1;
            return WorkResult::StillWorking;
        };

        // let debug = proof_to_specialize.conclusion() == formula!("(l=>((A l,E l)=(B l,F l))) = (l=>((C l,E l)=(D l,F l)))").to_rwm() && self.goal.conclusion == formula!("(l=>(((const A) l,(const E) l)=((const B) l,(const F) l))) = (l=>(((const C) l,(const E) l)=((const D) l,(const F) l)))").to_rwm();

        // if debug {
        //     dbg!()
        // }

        let Ok(mut substitutions) = proof_to_specialize
            .conclusion()
            .substitutions_to_become(&self.goal.conclusion)
        else {
            premises_tried.failed_hard();
            return WorkResult::StillWorking;
        };

        // if debug {
        //     dbg!()
        // }
        // dbg!(&premises_tried.next_trial);
        let premise_providers = premises_tried
            .next_trial
            .iter()
            .map(|&i| truths_for_my_premises.important_proofs[i].clone())
            .collect_vec();

        for (index, (premise, provider)) in
            zip(proof_to_specialize.premises(), &premise_providers).enumerate()
        {
            if premise
                .add_substitutions_to_become(&provider.conclusion(), &mut substitutions)
                .is_err()
            {
                premises_tried
                    .failed_at_premise(index, self.num_premise_candidates_at_last_iteration_start);
                return WorkResult::StillWorking;
            }
        }

        // if debug {
        //     dbg!()
        // }

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
            // already_tried_all_before: 0,
            proofs_tried: vec![],
            num_premise_candidates_at_last_iteration_start: 0,
            current_proof: 0,
        })
    }

    fn proof_discovered(&mut self, _proof: Proof) {
        self.goal_workers.wake_all()
    }
}
