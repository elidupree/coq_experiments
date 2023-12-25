use crate::introspective_calculus::proof_hierarchy::Proof;
use crate::introspective_calculus::solver_pool::{Goal, SolverPoolInner, SolverWorker};
use crate::introspective_calculus::RWMFormula;
use ai_framework::time_sharing;
use ai_framework::time_sharing::{TimeSharerKeyless, WorkResult};
use std::collections::BTreeSet;

struct GoalWorker {
    goal: Goal,
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
        if pool.get_goal(&self.goal).is_none() {
            context.completely_done();
            return WorkResult::Idle;
        }

        match pool.prove_by_substituting_with_transitive_equalities(
            &self.goal.premises,
            self.goal.conclusion.clone(),
        ) {
            None => WorkResult::Idle,
            Some(proof) => {
                // dbg!(&self.goal.conclusion, &self.goal.premises);
                WorkResult::ProducedOutput(proof)
            }
        }
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
        self.goal_workers.add_worker(GoalWorker { goal })
    }

    fn new_transitive_equality_discovered(&mut self) {
        self.goal_workers.wake_all()
    }
}

impl SolverPoolInner {
    pub fn prove_by_substituting_with_transitive_equalities(
        &self,
        premises: &BTreeSet<RWMFormula>,
        conclusion: RWMFormula,
    ) -> Option<Proof> {
        let sides = conclusion.as_eq_sides().unwrap();
        let paths = sides
            .clone()
            .map(|f| self.truths.by_premises[premises].path_to_equivalence_class_representative(f));

        if paths[0].representative != paths[1].representative {
            return None;
        }

        let mut running_proof = Proof::eq_refl(paths[0].representative.clone());
        let mut iters = paths.map(|path| path.links.into_iter().rev().fuse());
        loop {
            match iters.each_mut().map(Iterator::next) {
                [Some(a), Some(b)] if a.closer_formula == b.closer_formula => {
                    running_proof = Proof::eq_refl(a.closer_formula);
                }
                [None, None] => break,
                [a, b] => {
                    if let Some(a) = a {
                        running_proof = Proof::eq_trans_chain(&[
                            a.further_equals_closer_proof(),
                            running_proof,
                        ])
                        .unwrap();
                    }
                    if let Some(b) = b {
                        running_proof = Proof::eq_trans_chain(&[
                            running_proof,
                            b.closer_equals_further_proof(),
                        ])
                        .unwrap();
                    }
                }
            }
        }
        assert_eq!(running_proof.conclusion(), conclusion);
        assert!(running_proof.premises().is_subset(premises));
        Some(running_proof)
    }
}
