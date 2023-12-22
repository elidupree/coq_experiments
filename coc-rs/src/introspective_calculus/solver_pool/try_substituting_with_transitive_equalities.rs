use crate::introspective_calculus::proof_hierarchy::Proof;
use crate::introspective_calculus::solver_pool::{SolverPoolInner, SolverWorker};
use crate::introspective_calculus::RWMFormula;
use ai_framework::time_sharing;
use ai_framework::time_sharing::{TimeSharerKeyless, WorkResult};
use std::collections::BTreeSet;

struct GoalWorker {
    premises: BTreeSet<RWMFormula>,
    conclusion: RWMFormula,
}

impl time_sharing::Worker for GoalWorker {
    type Key = usize;
    type Workpiece = SolverPoolInner;
    type Output = Proof;

    fn do_some_work(
        &mut self,
        pool: &mut Self::Workpiece,
        _context: &mut time_sharing::WorkContext,
    ) -> WorkResult<Self::Output> {
        match pool.prove_by_substituting_with_transitive_equalities(
            &self.premises,
            self.conclusion.clone(),
        ) {
            None => WorkResult::Idle,
            Some(proof) => WorkResult::ProducedOutput(proof),
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

    fn goal_added(&mut self, premises: BTreeSet<RWMFormula>, conclusion: RWMFormula) {
        self.goal_workers.add_worker(GoalWorker {
            premises,
            conclusion,
        })
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
        Some(running_proof)
    }
}
//
// pub fn worker(pool: &mut SolverPoolInner) -> WorkResult<Option<Proof>> {
//     for (goal, goal_info) in &mut self.unsolved_goals {
//         if let Some(truth) = self
//             .known_truths
//             .truths
//             .get(goal_info.truths.len())
//             .cloned()
//         {
//             match self.known_truths.try_pair(truth.clone(), goal.clone()) {
//                 Ok(inference) => {
//                     return IncrementalDeriverWorkResult::DiscoveredInference(inference)
//                 }
//                 Err(info) => goal_info.truths.push(info),
//             }
//             return IncrementalDeriverWorkResult::StillWorking;
//         } else if goal_info.num_known_equalities_last_time_finished
//             < self.known_truths.equalities.len()
//             || goal_info.num_known_truths_last_time_finished < self.known_truths.truths.len()
//         {
//             let min = zip(
//                 self.known_truths.truths.iter().cloned(),
//                 &mut goal_info.truths,
//             )
//             .filter_map(|(t, g)| match g {
//                 GoalTruthPairInfo::CannotBeEqual => None,
//                 GoalTruthPairInfo::WasntEqualLastTimeWeChecked {
//                     num_known_equalities_that_time,
//                 } => {
//                     let n = *num_known_equalities_that_time;
//                     Some((t, g, n))
//                 }
//             })
//             .min_by_key(|(_t, _g, i)| *i);
//             if let Some((t, g, i)) = min {
//                 if i < self.known_truths.equalities.len() {
//                     match self.known_truths.try_pair(t.clone(), goal.clone()) {
//                         Ok(inference) => {
//                             return IncrementalDeriverWorkResult::DiscoveredInference(inference)
//                         }
//                         Err(info) => *g = info,
//                     }
//                     return IncrementalDeriverWorkResult::StillWorking;
//                 }
//             }
//             goal_info.num_known_equalities_last_time_finished = self.known_truths.equalities.len();
//             goal_info.num_known_truths_last_time_finished = self.known_truths.truths.len();
//         }
//     }
// }
