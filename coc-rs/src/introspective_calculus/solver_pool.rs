mod discover_unfoldings;
mod try_internally_specializing_proven_ucfes;
mod try_specializing_proven_inferences;
mod try_substituting_with_transitive_equalities;

use crate::introspective_calculus::inference::{load_proof, Inference, ProofScript};
use crate::introspective_calculus::proof_hierarchy::{Proof, Proven};
use crate::introspective_calculus::provers::ByAssumingIt;
use crate::introspective_calculus::raw_proofs::ALL_CORE_RULES;
use crate::introspective_calculus::uncurried_function::UncurriedFunctionEquivalence;
use crate::introspective_calculus::{Formula, RWMFormula};
use ai_framework::time_sharing;
use ai_framework::time_sharing::{TimeSharer, WorkResult};
use hash_capsule::BuildHasherForHashCapsules;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::iter;
use std::sync::{LazyLock, Mutex};

enum FormulaTransitiveEqualitiesEntry {
    RepresentativeOfClass,
    ProvenEqualToOtherFormulaCloserToRepresentativeBy(Proof),
}
#[derive(Default)]
pub struct KnownTruthsForPremises {
    important_proofs: Vec<Proof>,
    unimportant_proofs: Vec<Proof>,
    important_proven_ucfes: Vec<Proven<UncurriedFunctionEquivalence>>,
    proofs_by_conclusion: HashMap<RWMFormula, Proof, BuildHasherForHashCapsules>,
    transitive_equalities:
        HashMap<RWMFormula, FormulaTransitiveEqualitiesEntry, BuildHasherForHashCapsules>,
}
#[derive(Default)]
pub struct KnownTruths {
    important_proofs: Vec<Proof>,
    unimportant_proofs: Vec<Proof>,
    by_premises: BTreeMap<BTreeSet<RWMFormula>, KnownTruthsForPremises>,
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Goal {
    pub premises: BTreeSet<RWMFormula>,
    pub conclusion: RWMFormula,
}

#[derive(Default)]
pub struct GoalInfo {}

#[derive(Default)]
pub struct GoalConclusion {
    by_premises: BTreeMap<BTreeSet<RWMFormula>, GoalInfo>,
}
#[derive(Default)]
pub struct Goals {
    by_conclusion: HashMap<RWMFormula, GoalConclusion>,
}

#[derive(Default)]
pub struct SolverPoolInner {
    truths: KnownTruths,
    goals: Goals,
    unfolding_visited: HashSet<RWMFormula, BuildHasherForHashCapsules>,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum GlobalSolverId {
    DiscoverUnfoldings,
    TrySpecializingProvenInferences,
    TryInternallySpecializingProvenUcfes,
    TrySubstitutingWithTransitiveEqualities,
}

trait SolverWorker: Send + Sync + 'static {
    fn do_some_work(&mut self, pool: &mut SolverPoolInner) -> WorkResult<Proof>;

    fn consider_unfolding(&mut self, _formula: RWMFormula) {}
    fn goal_added(&mut self, _goal: Goal) {}
    fn proof_discovered(&mut self, _proof: Proof) {}
    fn new_transitive_equality_discovered(&mut self) {}
}

// type SolverWorkerFn = WorkerFn<SolverPoolInner, Proof>;
// type SimpleSolverTimeSharer = TimeSharerKeyless<SolverWorkerFn>;

impl time_sharing::Worker for Box<dyn SolverWorker> {
    type Key = GlobalSolverId;
    type Workpiece = SolverPoolInner;
    type Output = Proof;

    fn do_some_work(
        &mut self,
        workpiece: &mut Self::Workpiece,
        _context: &mut time_sharing::WorkContext,
    ) -> WorkResult<Self::Output> {
        SolverWorker::do_some_work(&mut **self, workpiece)
    }
}

pub struct SolverPool {
    inner: SolverPoolInner,
    sharer: TimeSharer<Box<dyn SolverWorker>>,
}

impl Default for SolverPool {
    fn default() -> Self {
        let mut sharer: TimeSharer<Box<dyn SolverWorker>> = TimeSharer::default();
        use GlobalSolverId::*;
        sharer.add_worker(
            DiscoverUnfoldings,
            Box::<discover_unfoldings::Worker>::default(),
        );
        sharer.add_worker(
            TrySpecializingProvenInferences,
            Box::<try_specializing_proven_inferences::Worker>::default(),
        );
        sharer.add_worker(
            TryInternallySpecializingProvenUcfes,
            Box::<try_internally_specializing_proven_ucfes::Worker>::default(),
        );
        sharer.add_worker(
            TrySubstitutingWithTransitiveEqualities,
            Box::<try_substituting_with_transitive_equalities::Worker>::default(),
        );
        let mut result = SolverPool {
            inner: SolverPoolInner::default(),
            sharer,
        };
        for rule in &*ALL_CORE_RULES {
            result.discover_proof(rule.to_proof(), true);
        }
        result
    }
}
#[derive(Default)]
struct DiscoverResult {
    new_transitive_equalities: bool,
}

impl SolverPool {
    pub fn do_some_work(&mut self) -> WorkResult<Proof> {
        let result = self.sharer.do_some_work(&mut self.inner);
        if let WorkResult::ProducedOutput(proof) = &result {
            self.discover_proof(proof.clone(), false);
        }
        result
    }

    pub fn add_goal(&mut self, goal: Goal) {
        self.sharer.wake_all();
        for worker in self.sharer.workers_mut() {
            worker.goal_added(goal.clone())
        }
        for proposition in goal.premises.iter().chain(iter::once(&goal.conclusion)) {
            for side in proposition.as_eq_sides().unwrap() {
                self.consider_unfolding(side);
            }
        }
        self.inner.add_goal(goal);
    }

    pub fn discover_proof(&mut self, proof: Proof, known_important: bool) {
        //TODO: update bootstrapped-ness

        // (it could be None if we're generating unfoldings / making synthetic truths rather than solving goals)
        let mut solves_any_goal = false;
        if let Some(c) = self.inner.goals.by_conclusion.get_mut(&proof.conclusion()) {
            let before = c.by_premises.len();
            c.by_premises
                .retain(|premises, _info| !proof.premises().is_subset(premises));
            if c.by_premises.len() < before {
                solves_any_goal = true;
            }
        }
        let is_important = known_important || solves_any_goal;
        // dbg!(proof.conclusion(), proof.premises());
        self.sharer
            .wake(&GlobalSolverId::TrySpecializingProvenInferences);
        self.sharer
            .wake(&GlobalSolverId::TryInternallySpecializingProvenUcfes);
        for worker in self.sharer.workers_mut() {
            worker.proof_discovered(proof.clone());
        }
        let discover_result = self.inner.truths.discover(proof, is_important);
        if discover_result.new_transitive_equalities {
            self.sharer
                .wake(&GlobalSolverId::TrySubstitutingWithTransitiveEqualities);
            for worker in self.sharer.workers_mut() {
                worker.new_transitive_equality_discovered();
            }
        }
    }

    pub fn get_existing_proof(&self, goal: &Goal) -> Option<Proof> {
        self.inner
            .truths
            .by_premises
            .get(&goal.premises)?
            .proofs_by_conclusion
            .get(&goal.conclusion)
            .cloned()
    }

    pub fn solve(&mut self, goal: &Goal) -> Proof {
        loop {
            if let Some(result) = self.get_existing_proof(goal) {
                return result;
            }
            self.do_some_work();
        }
    }

    // pub fn try_prove(&mut self, goal: Inference) -> Result<Proof, String> {
    //     while let WorkResult::DidSomeWork(result) = self.do_some_work() {
    //         if let Some(new_proof) = result {
    //             if new_proof_proves_goal {
    //                 return Ok(new_proof);
    //             }
    //         }
    //     }
    //     Err(format!("finished searching without proving {goal}"))
    // }
}

impl KnownTruths {
    fn discover(&mut self, proof: Proof, is_important: bool) -> DiscoverResult {
        if is_important {
            self.important_proofs.push(proof.clone());
        } else {
            self.unimportant_proofs.push(proof.clone());
        }
        let mut result = DiscoverResult::default();
        for (premises, truths) in &mut self.by_premises {
            if proof.premises().is_subset(premises) {
                let subresult = truths.discover(proof.clone(), is_important);
                if subresult.new_transitive_equalities {
                    result.new_transitive_equalities = true;
                }
            }
        }
        result
    }
}

struct PathToEquivalenceClassRepresentativeLink {
    proof: Proof,
    closer_formula: RWMFormula,
    further_formula: RWMFormula,
}
struct PathToEquivalenceClassRepresentative {
    representative: RWMFormula,
    links: Vec<PathToEquivalenceClassRepresentativeLink>,
}
impl PathToEquivalenceClassRepresentativeLink {
    pub fn closer_equals_further_proof(&self) -> Proof {
        if self.proof.conclusion().as_eq_sides().unwrap()[0] == self.closer_formula {
            self.proof.clone()
        } else {
            self.proof.flip_conclusion()
        }
    }
    pub fn further_equals_closer_proof(&self) -> Proof {
        if self.proof.conclusion().as_eq_sides().unwrap()[0] == self.further_formula {
            self.proof.clone()
        } else {
            self.proof.flip_conclusion()
        }
    }
}
impl KnownTruthsForPremises {
    // path of formulas (containing `formula`) and path of inferences that is 1 shorter
    fn path_to_equivalence_class_representative(
        &self,
        formula: RWMFormula,
    ) -> PathToEquivalenceClassRepresentative {
        let mut links = Vec::new();
        let mut running_formula = formula.clone();

        while let Some(
            FormulaTransitiveEqualitiesEntry::ProvenEqualToOtherFormulaCloserToRepresentativeBy(
                proof,
            ),
        ) = self.transitive_equalities.get(&running_formula)
        {
            let further_formula = running_formula;
            let closer_formula = proof.conclusion().other_eq_side(&further_formula).unwrap();
            running_formula = closer_formula.clone();
            links.push(PathToEquivalenceClassRepresentativeLink {
                proof: proof.clone(),
                closer_formula,
                further_formula,
            });
        }
        if let Some(first) = links.first() {
            assert_eq!(first.further_formula, formula)
        } else {
            assert_eq!(running_formula, formula)
        }
        PathToEquivalenceClassRepresentative {
            representative: running_formula,
            links,
        }
    }
    fn discover(&mut self, proof: Proof, is_important: bool) -> DiscoverResult {
        if is_important {
            self.important_proofs.push(proof.clone());
            if let Ok(f) = proof.conclusion().already_uncurried_function_equivalence() {
                self.important_proven_ucfes
                    .push(Proven::new(f, proof.clone()));
            }
        } else {
            self.unimportant_proofs.push(proof.clone());
        }
        self.proofs_by_conclusion
            .insert(proof.conclusion(), proof.clone());
        let mut result = DiscoverResult::default();

        let sides = proof.conclusion().as_eq_sides().unwrap();

        let paths = sides
            .clone()
            .map(|f| self.path_to_equivalence_class_representative(f));

        if paths[0].representative == paths[1].representative {
            return result;
        }

        result.new_transitive_equalities = true;

        let [a, b] = sides;
        // leave B as-is and make the whole A tree flow towards it:
        self.transitive_equalities
            .entry(b.clone())
            .or_insert(FormulaTransitiveEqualitiesEntry::RepresentativeOfClass);
        self.transitive_equalities.insert(
            a.clone(),
            FormulaTransitiveEqualitiesEntry::ProvenEqualToOtherFormulaCloserToRepresentativeBy(
                proof,
            ),
        );

        let [a, _] = paths;
        for link in a.links {
            *self
                .transitive_equalities
                .get_mut(&link.closer_formula)
                .unwrap() =
                FormulaTransitiveEqualitiesEntry::ProvenEqualToOtherFormulaCloserToRepresentativeBy(
                    link.proof,
                );
        }
        result
    }
}

// impl FromIterator<Proof> for KnownTruthsForPremises {
//     fn from_iter<T: IntoIterator<Item = Proof>>(iter: T) -> Self {
//         let mut result = Self::default();
//         for proof in iter {
//             result.discover(proof, true);
//         }
//         result
//     }
// }

impl SolverPool {
    pub fn has_goal(&self, goal: &Goal) -> bool {
        self.inner.get_goal(goal).is_some()
    }
}

impl SolverPoolInner {
    fn get_goal(&self, goal: &Goal) -> Option<&GoalInfo> {
        self.goals
            .by_conclusion
            .get(&goal.conclusion)
            .and_then(|g| g.by_premises.get(&goal.premises))
    }

    fn add_goal(&mut self, goal: Goal) {
        self.goals
            .by_conclusion
            .entry(goal.conclusion.clone())
            .or_default()
            .by_premises
            .entry(goal.premises.clone())
            .or_default();
        self.truths
            .by_premises
            .entry(goal.premises.clone())
            .or_insert_with(|| {
                let mut result = KnownTruthsForPremises::default();
                for premise in &goal.premises {
                    result.discover(premise.prove(ByAssumingIt), true);
                }
                for proof in &self.truths.important_proofs {
                    if proof.premises().is_subset(&goal.premises) {
                        result.discover(proof.clone(), true);
                    }
                }
                for proof in &self.truths.unimportant_proofs {
                    if proof.premises().is_subset(&goal.premises) {
                        result.discover(proof.clone(), false);
                    }
                }
                result
            });
    }
}

impl Goal {
    pub fn in_arbitrary_order(&self) -> Inference {
        Inference::new(
            self.premises.iter().cloned().collect(),
            self.conclusion.clone(),
        )
    }
}

/**********************************************************
Scripts stuff (should it really be in this file?)
 */

pub static ALL_PROOF_SCRIPTS: LazyLock<HashMap<String, ProofScript>> = LazyLock::new(|| {
    std::fs::read_dir("./data/ic_proofs")
        .unwrap()
        .filter_map(|entry| {
            let path = entry.unwrap().path();
            let name = path.file_name().unwrap().to_str().unwrap();
            Some((
                name.to_string(),
                ProofScript::new(&load_proof(&path).ok()?).ok()?,
            ))
        })
        .collect()
});

pub static GLOBAL_SOLVER: LazyLock<Mutex<SolverPool>> = LazyLock::new(|| {
    let mut pool = SolverPool::default();
    for script in ALL_PROOF_SCRIPTS.values() {
        let premises: BTreeSet<RWMFormula> = script.premises.iter().map(Formula::to_rwm).collect();
        for conclusion in &script.conclusions {
            pool.add_goal(Goal {
                premises: premises.clone(),
                conclusion: conclusion.to_rwm(),
            })
        }
    }
    Mutex::new(pool)
});
