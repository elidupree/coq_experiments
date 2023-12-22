use crate::introspective_calculus::proof_hierarchy::Proof;
use crate::introspective_calculus::solver_pool::{
    GlobalSolverId, SolverPool, SolverPoolInner, SolverWorker,
};
use crate::introspective_calculus::RWMFormula;
use ai_framework::time_sharing;
use ai_framework::time_sharing::{TimeSharerOwned, WorkResult};

impl SolverPool {
    pub fn consider_unfolding(&mut self, formula: RWMFormula) {
        if self.inner.unfolding_visited.insert(formula.clone()) {
            self.sharer.wake(&GlobalSolverId::DiscoverUnfoldings);
            self.sharer
                .get_mut(&GlobalSolverId::DiscoverUnfoldings)
                .unwrap()
                .consider_unfolding(formula);
        }
    }
}

pub struct SingleFormulaWorker {
    current_formula: RWMFormula,
    steps_taken: u32,
}

impl time_sharing::Worker for SingleFormulaWorker {
    type Key = RWMFormula;
    type Workpiece = SolverPoolInner;
    type Output = Proof;

    fn do_some_work(
        &mut self,
        pool: &mut Self::Workpiece,
        context: &mut time_sharing::WorkContext,
    ) -> WorkResult<Self::Output> {
        if let Some(proof) = self.current_formula.unfold_any_one_subformula_proof() {
            let [a, b] = proof.conclusion().as_eq_sides().unwrap();
            assert_eq!(a, self.current_formula);
            let is_fresh = pool.unfolding_visited.insert(b.clone());
            self.current_formula = b;
            self.steps_taken += 1;
            if self.steps_taken >= 100 || !is_fresh {
                context.completely_done();
            }
            WorkResult::ProducedOutput(proof)
        } else {
            context.completely_done();
            WorkResult::Idle
        }
    }
}

#[derive(Default)]
pub struct Worker {
    unfolding_formulas: TimeSharerOwned<SingleFormulaWorker>,
}

impl SolverWorker for Worker {
    fn do_some_work(&mut self, pool: &mut SolverPoolInner) -> WorkResult<Proof> {
        self.unfolding_formulas.do_some_work()
    }

    fn consider_unfolding(&mut self, formula: RWMFormula) {
        self.unfolding_formulas.add_worker(
            formula.clone(),
            SingleFormulaWorker {
                current_formula: formula,
                steps_taken: 0,
            },
        )
    }
}
