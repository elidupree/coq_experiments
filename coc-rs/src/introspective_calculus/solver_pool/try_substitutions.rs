use crate::introspective_calculus::proof_hierarchy::ProofWithPremises;
use crate::introspective_calculus::solver_pool::SolverPoolInner;
use ai_framework::time_sharing::WorkResult;

pub fn worker(pool: &mut SolverPoolInner) -> WorkResult<Option<ProofWithPremises>> {}
