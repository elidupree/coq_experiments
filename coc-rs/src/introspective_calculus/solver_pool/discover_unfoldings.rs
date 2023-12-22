use crate::introspective_calculus::proof_hierarchy::Proof;
use crate::introspective_calculus::solver_pool::{GlobalSolverId, SolverPool, SolverPoolInner};
use crate::introspective_calculus::RWMFormula;
use ai_framework::time_sharing::WorkResult;

impl SolverPoolInner {
    pub fn consider_unfolding(&mut self, formula: RWMFormula, steps_already: usize) {
        if steps_already < 100 && self.unfolding_visited.insert(formula.clone()) {
            self.unfolding_queue.push_back((formula, steps_already));
        }
    }
}
impl SolverPool {
    pub fn consider_unfolding(&mut self, formula: RWMFormula) {
        self.inner.consider_unfolding(formula, 0);
        self.sharer.wake(&GlobalSolverId::DiscoverUnfoldings)
    }
}

pub fn worker(pool: &mut SolverPoolInner) -> WorkResult<Option<Proof>> {
    if let Some((f, steps)) = pool.unfolding_queue.pop_front() {
        if let Some(proof) = f.unfold_any_one_subformula_proof() {
            let [a, b] = proof.conclusion().as_eq_sides().unwrap();
            assert_eq!(a, f);
            pool.consider_unfolding(b, steps + 1);
            WorkResult::StillWorking(Some(proof))
        } else {
            WorkResult::StillWorking(None)
        }
    } else {
        WorkResult::NothingToDo
    }
}
