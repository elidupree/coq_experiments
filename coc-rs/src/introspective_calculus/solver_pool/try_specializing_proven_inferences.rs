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
