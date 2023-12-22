mod discover_unfoldings;
mod try_specializing_proven_inferences;
mod try_substitutions;

use crate::introspective_calculus::proof_hierarchy::Proof;
use crate::introspective_calculus::RWMFormula;
use ai_framework::time_sharing;
use ai_framework::time_sharing::{TimeSharer, WorkResult};
use hash_capsule::BuildHasherForHashCapsules;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

enum FormulaTransitiveEqualitiesEntry {
    RepresentativeOfClass,
    ProvenEqualToOtherFormulaCloserToRepresentativeBy(Proof),
}
#[derive(Default)]
pub struct KnownTruthsForPremises {
    proofs: Vec<Proof>,
    transitive_equalities:
        HashMap<RWMFormula, FormulaTransitiveEqualitiesEntry, BuildHasherForHashCapsules>,
}
#[derive(Default)]
pub struct KnownTruths {
    proofs: Vec<Proof>,
    by_premises: BTreeMap<BTreeSet<RWMFormula>, KnownTruthsForPremises>,
}

pub struct Goal {}

pub struct GoalConclusion {
    by_premises: BTreeMap<BTreeSet<RWMFormula>, Goal>,
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

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum GlobalSolverId {
    DiscoverUnfoldings,
    TrySpecializingProvenInferences,
    TrySubstitutions,
}

trait SolverWorker: Send + Sync + 'static {
    fn do_some_work(&mut self, pool: &mut SolverPoolInner) -> WorkResult<Proof>;

    fn consider_unfolding(&mut self, _formula: RWMFormula) {}
}

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
            Box::new(self::discover_unfoldings::Worker::default()),
        );
        sharer.add_worker(
            TrySpecializingProvenInferences,
            Box::new(self::try_specializing_proven_inferences::Worker::default()),
        );
        sharer.add_worker(
            TrySubstitutions,
            Box::new(self::try_substitutions::Worker::default()),
        );
        SolverPool {
            inner: SolverPoolInner::default(),
            sharer,
        }
    }
}
impl SolverPool {
    pub fn do_some_work(&mut self) -> WorkResult<Proof> {
        self.sharer.do_some_work(&mut self.inner)
    }

    pub fn add_goal(&mut self, premises: BTreeSet<RWMFormula>, conclusion: RWMFormula) {
        self.sharer.wake_all();
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
    pub fn discover(&mut self, proof: Proof) {
        self.proofs.push(proof.clone());
        self.by_premises
            .entry(proof.premises().clone())
            .or_insert_with(Default::default)
            .discover(proof);
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

impl KnownTruthsForPremises {
    // path of formulas (containing `formula`) and path of inferences that is 1 shorter
    fn path_to_equivalence_class_representative(
        &self,
        formula: RWMFormula,
    ) -> PathToEquivalenceClassRepresentative {
        let mut links = Vec::new();
        let mut running_formula = formula;

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
        PathToEquivalenceClassRepresentative {
            representative: running_formula,
            links,
        }
    }
    pub fn discover(&mut self, proof: Proof) {
        self.proofs.push(proof.clone());

        let sides = proof.conclusion().as_eq_sides().unwrap();

        let paths = sides
            .clone()
            .map(|f| self.path_to_equivalence_class_representative(f));
        if paths[0].representative == paths[1].representative {
            return;
        }

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
    }
}
