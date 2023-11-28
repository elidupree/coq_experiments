use crate::introspective_calculus::derivers::{IncrementalDeriver, IncrementalDeriverWorkResult};
use crate::introspective_calculus::inference::ProvenInference;
use crate::introspective_calculus::{RWMFormula, RWMFormulaValue};
use crate::{ic, substitutions};
use hash_capsule::BuildHasherForHashCapsules;
use live_prop_test::live_prop_test;
use std::collections::{HashMap, HashSet, VecDeque};
use std::iter::zip;

enum FormulaEqualityInfo {
    RepresentativeOfClass,
    ProvenEqualToOtherFormulaCloserToRepresentativeBy(ProvenInference),
}

enum GoalTruthPairInfo {
    CannotBeEqual,
    WasntEqualLastTimeWeChecked {
        num_known_equalities_that_time: usize,
    },
}

struct GoalInfo {
    truths: Vec<GoalTruthPairInfo>,
    num_known_equalities_last_time_finished: usize,
    num_known_truths_last_time_finished: usize,
}

/// maintain a collection of all known equalities and try to use them to equate (known truth, unsolved goal) pairs
pub struct DeriveBySubstitutionAndUnfolding {
    unsolved_goals: HashMap<RWMFormula, GoalInfo, BuildHasherForHashCapsules>,
    unfolding_heads: VecDeque<(RWMFormula, usize)>,
    unfolding_visited: HashSet<RWMFormula, BuildHasherForHashCapsules>,
    known_truths: KnownTruths,
}

#[derive(Default)]
struct KnownTruths {
    available_premises: Vec<RWMFormula>,
    // inferences starting from the premises
    truths: Vec<ProvenInference>,
    equalities: HashMap<RWMFormula, FormulaEqualityInfo>,
}

#[live_prop_test]
impl KnownTruths {
    // path of formulas (containing `formula`) and path of inferences that is 1 shorter
    fn path_to_representative(
        &self,
        formula: RWMFormula,
    ) -> (Vec<RWMFormula>, Vec<ProvenInference>) {
        let mut formulas = vec![formula.clone()];
        let mut running_formula = formula;

        let mut inferences = Vec::new();
        while let Some(FormulaEqualityInfo::ProvenEqualToOtherFormulaCloserToRepresentativeBy(
            inference,
        )) = self.equalities.get(&running_formula)
        {
            running_formula = inference
                .conclusion
                .other_eq_side(&running_formula)
                .unwrap();
            formulas.push(running_formula.clone());
            inferences.push(inference.clone());
        }
        (formulas, inferences)
    }

    fn try_pair(
        &self,
        truth: ProvenInference,
        goal: RWMFormula,
    ) -> Result<ProvenInference, GoalTruthPairInfo> {
        if let Some(proof) = self.known_equality_proof([truth.conclusion.clone(), goal.clone()]) {
            let c = ProvenInference::substitute_whole_formula()
                .specialize(&substitutions!("A" := &truth.conclusion, "B" := goal));
            return Ok(ProvenInference::chain(
                self.available_premises.clone(),
                vec![proof, truth],
                c,
            )
            .unwrap());
        }

        Err(GoalTruthPairInfo::WasntEqualLastTimeWeChecked {
            num_known_equalities_that_time: self.equalities.len(),
        })
    }

    #[live_prop_test(
        postcondition = "result.as_ref().map_or(true, |r| r.conclusion.as_eq_sides().unwrap() == old(formulas.clone()))"
    )]
    fn known_equality_proof(&self, formulas: [RWMFormula; 2]) -> Option<ProvenInference> {
        let paths = formulas.clone().map(|f| self.path_to_representative(f));
        let representatives = paths.each_ref().map(|(f, _i)| f.last().unwrap());
        if representatives[0] == representatives[1] {
            // TODO maybe: make this more efficient by popping shared tail from paths
            let mut proof = ProvenInference::derive_by(
                "eq_refl",
                &[],
                &ic!({ formulas[0] } = { formulas[0] }).to_rwm(),
            )
            .unwrap();
            proof = ProvenInference::chain(self.available_premises.clone(), vec![], proof).unwrap();
            let mut extend_proof_with = |mut inference: ProvenInference| {
                // println!("{} with {}", proof, inference);
                let [a, b] = proof.conclusion.as_eq_sides().unwrap();
                let [c, d] = inference.conclusion.as_eq_sides().unwrap();
                if b == d {
                    // println!("flipping {}", inference);
                    let i2 = ProvenInference::derive_by(
                        "eq_sym",
                        &[&inference.conclusion],
                        &ic!(d = c).to_rwm(),
                    )
                    .unwrap();
                    inference = ProvenInference::chain(
                        self.available_premises.clone(),
                        vec![inference],
                        i2,
                    )
                    .unwrap();
                }
                let [_c, d] = inference.conclusion.as_eq_sides().unwrap();
                let i3 = ProvenInference::derive_by(
                    "eq_trans",
                    &[&proof.conclusion, &inference.conclusion],
                    &ic!(a = d).to_rwm(),
                )
                .unwrap();
                // println!("{proof}, {inference}");
                proof = ProvenInference::chain(
                    self.available_premises.clone(),
                    vec![proof.clone(), inference],
                    i3,
                )
                .unwrap();
            };

            let [(_, a_inferences), (_, b_inferences)] = paths;
            for inference in a_inferences {
                extend_proof_with(inference);
            }
            for inference in b_inferences.into_iter().rev() {
                extend_proof_with(inference);
            }
            return Some(proof);
        }

        // not known equal outright, but try a compound proof:
        if let [RWMFormulaValue::Apply([al, ar]), RWMFormulaValue::Apply([bl, br])] =
            formulas.each_ref().map(RWMFormula::value)
        {
            if let Some(il) = self.known_equality_proof([al.clone(), bl.clone()]) {
                if let Some(ir) = self.known_equality_proof([ar.clone(), br.clone()]) {
                    let conclusion_provider = ProvenInference::derive_by(
                        "compatibility_both",
                        &[&il.conclusion, &ir.conclusion],
                        &ic!((al ar) = (bl br)).to_rwm(),
                    )
                    .unwrap();
                    return Some(
                        ProvenInference::chain(
                            self.available_premises.clone(),
                            vec![il, ir],
                            conclusion_provider,
                        )
                        .unwrap(),
                    );
                }
            }
        }

        None
    }

    fn proven(&mut self, proof: ProvenInference) {
        assert_eq!(proof.premises, self.available_premises);
        self.truths.push(proof.clone());
        let Some(sides) = proof.conclusion.as_eq_sides() else {
            return;
        };

        let paths = sides.clone().map(|f| self.path_to_representative(f));
        let representatives = paths.each_ref().map(|(f, _i)| f.last().unwrap());
        if representatives[0] == representatives[1] {
            return;
        }

        let [a, b] = sides;
        // leave B as-is and make the whole A tree flow towards it:
        self.equalities
            .entry(b.clone())
            .or_insert(FormulaEqualityInfo::RepresentativeOfClass);
        self.equalities.insert(
            a.clone(),
            FormulaEqualityInfo::ProvenEqualToOtherFormulaCloserToRepresentativeBy(proof),
        );

        let [(a_formulas, a_inferences), _] = paths;
        for (formula, inference) in zip(&a_formulas[1..], a_inferences) {
            *self.equalities.get_mut(formula).unwrap() =
                FormulaEqualityInfo::ProvenEqualToOtherFormulaCloserToRepresentativeBy(inference);
        }
    }
}

impl DeriveBySubstitutionAndUnfolding {
    pub fn new(available_premises: Vec<RWMFormula>) -> DeriveBySubstitutionAndUnfolding {
        DeriveBySubstitutionAndUnfolding {
            known_truths: KnownTruths {
                available_premises,
                truths: vec![],
                equalities: Default::default(),
            },
            unsolved_goals: HashMap::with_hasher(Default::default()),
            unfolding_heads: Default::default(),
            unfolding_visited: HashSet::with_hasher(Default::default()),
        }
    }
}

impl IncrementalDeriver for DeriveBySubstitutionAndUnfolding {
    fn description(&self) -> String {
        "DeriveBySubstitutionAndUnfolding".to_string()
    }

    fn add_goal(&mut self, goal: RWMFormula) {
        if self.unfolding_visited.insert(goal.clone()) {
            self.unfolding_heads.push_front((goal.clone(), 0));
        }
        self.unsolved_goals.insert(
            goal,
            GoalInfo {
                truths: vec![],
                num_known_equalities_last_time_finished: 0,
                num_known_truths_last_time_finished: 0,
            },
        );
    }

    fn goal_got_proven(&mut self, proof: ProvenInference) {
        if self.unfolding_visited.insert(proof.conclusion.clone()) {
            self.unfolding_heads
                .push_front((proof.conclusion.clone(), 0));
        }
        self.unsolved_goals.remove(&proof.conclusion);
        self.known_truths.proven(proof);
    }

    fn do_some_work(&mut self) -> IncrementalDeriverWorkResult {
        if let Some((head, steps)) = self.unfolding_heads.pop_front() {
            if steps < 100 {
                if let Some(inference) = head.unfold_any_one_subformula_equality_inference() {
                    let [a, b] = inference.conclusion.as_eq_sides().unwrap();
                    assert_eq!(a, head);
                    if self.unfolding_visited.insert(b.clone()) {
                        self.unfolding_heads.push_back((b, steps + 1));
                    }
                    self.known_truths.proven(
                        ProvenInference::chain(
                            self.known_truths.available_premises.clone(),
                            vec![],
                            inference,
                        )
                        .unwrap(),
                    );
                }
            }
        }
        for (goal, goal_info) in &mut self.unsolved_goals {
            if let Some(truth) = self
                .known_truths
                .truths
                .get(goal_info.truths.len())
                .cloned()
            {
                match self.known_truths.try_pair(truth.clone(), goal.clone()) {
                    Ok(inference) => {
                        return IncrementalDeriverWorkResult::DiscoveredInference(inference)
                    }
                    Err(info) => goal_info.truths.push(info),
                }
                return IncrementalDeriverWorkResult::StillWorking;
            } else if goal_info.num_known_equalities_last_time_finished
                < self.known_truths.equalities.len()
                || goal_info.num_known_truths_last_time_finished < self.known_truths.truths.len()
            {
                let min = zip(
                    self.known_truths.truths.iter().cloned(),
                    &mut goal_info.truths,
                )
                .filter_map(|(t, g)| match g {
                    GoalTruthPairInfo::CannotBeEqual => None,
                    GoalTruthPairInfo::WasntEqualLastTimeWeChecked {
                        num_known_equalities_that_time,
                    } => {
                        let n = *num_known_equalities_that_time;
                        Some((t, g, n))
                    }
                })
                .min_by_key(|(_t, _g, i)| *i);
                if let Some((t, g, i)) = min {
                    if i < self.known_truths.equalities.len() {
                        match self.known_truths.try_pair(t.clone(), goal.clone()) {
                            Ok(inference) => {
                                return IncrementalDeriverWorkResult::DiscoveredInference(inference)
                            }
                            Err(info) => *g = info,
                        }
                        return IncrementalDeriverWorkResult::StillWorking;
                    }
                }
                goal_info.num_known_equalities_last_time_finished =
                    self.known_truths.equalities.len();
                goal_info.num_known_truths_last_time_finished = self.known_truths.truths.len();
            }
        }
        IncrementalDeriverWorkResult::NothingToDoRightNow
    }
}
