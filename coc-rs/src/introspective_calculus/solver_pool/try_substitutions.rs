use crate::introspective_calculus::proof_hierarchy::Proof;
use crate::introspective_calculus::solver_pool::{SolverPoolInner, SolverWorker};
use ai_framework::time_sharing::WorkResult;

#[derive(Default)]
pub struct Worker {}

impl SolverWorker for Worker {
    fn do_some_work(&mut self, pool: &mut SolverPoolInner) -> WorkResult<Proof> {
        todo!()
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
