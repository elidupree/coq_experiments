use crate::introspective_calculus::inference::ProvenInference;
use crate::introspective_calculus::proof_hierarchy::ProofWithVariables;
use crate::introspective_calculus::provers::BySubstitutingWith;
use crate::introspective_calculus::raw_proofs::{CleanExternalRule, Rule};
use crate::introspective_calculus::{RWMFormula, RWMFormulaValue};
use crate::{ic, match_ic, substitutions};
use live_prop_test::live_prop_test;

#[live_prop_test]
impl RWMFormula {
    pub fn unfold_here(&mut self) -> bool {
        match_ic!(self, {
            ((const a) _b) => {*self = a.to_rwm(); true },
            (((fuse a) b) c) => {*self = ic!((a c)(b c)).to_rwm(); true },
            _ => false,
        })
    }
    pub fn unfold_here_proof(&self) -> Option<ProofWithVariables> {
        match_ic!(self, {
            ((const a) b) => {
                Some(ProofWithVariables::new(
                    Rule::from(CleanExternalRule::DefinitionOfConst).specialize (
                    substitutions!(A: a, B: b)
                ), vec![]
                ).unwrap())
            },
            (((fuse a) b) c) => {
                Some(ProofWithVariables::new(
                    Rule::from(CleanExternalRule::DefinitionOfFuse).specialize (
                    substitutions!(A: a, B: b, C: c)
                ), vec![]
                ).unwrap())
            },
            _ => None,
        })
    }
    pub fn unfold_here_equality_inference(&self) -> Option<ProvenInference> {
        match_ic!(self, {
            ((const a) b) => {
                Some(ProvenInference::definition_of_const().specialize (
                    &substitutions!(A: a, B: b)
                ))
            },
            (((fuse a) b) c) => {
                Some(ProvenInference::definition_of_fuse().specialize (
                    &substitutions!(A: a, B: b, C: c)
                ))
            },
            _ => None,
        })
    }

    pub fn unfold_any_one_subformula_proof(&self) -> Option<ProofWithVariables> {
        if let Some(result) = self.unfold_here_proof() {
            return Some(result);
        }
        if let RWMFormulaValue::Apply([l, r]) = self.value() {
            if let Some(subresult) = l.unfold_any_one_subformula_proof() {
                let [a, b] = subresult.conclusion().as_eq_sides().unwrap();
                return Some(ic!((a r) = (b r)).prove(BySubstitutingWith(&[subresult])));
            }
            if let Some(subresult) = r.unfold_any_one_subformula_proof() {
                let [a, b] = subresult.conclusion().as_eq_sides().unwrap();
                return Some(ic!((l a) = (l b)).prove(BySubstitutingWith(&[subresult])));
            }
        }

        None
    }

    pub fn unfold_any_one_subformula_equality_inference(&self) -> Option<ProvenInference> {
        if let Some(result) = self.unfold_here_equality_inference() {
            return Some(result);
        }
        if let RWMFormulaValue::Apply([l, r]) = self.value() {
            if let Some(subresult) = l.unfold_any_one_subformula_equality_inference() {
                let [a, b] = subresult.conclusion.as_eq_sides().unwrap();
                return Some(
                    ProvenInference::chain(
                        vec![],
                        vec![subresult.clone()],
                        ProvenInference::compatibility_left()
                            .specialize(&substitutions!(A: a, B: b, C: r)),
                    )
                    .unwrap(),
                );
            }
            if let Some(subresult) = r.unfold_any_one_subformula_equality_inference() {
                let [a, b] = subresult.conclusion.as_eq_sides().unwrap();
                return Some(
                    ProvenInference::chain(
                        vec![],
                        vec![subresult.clone()],
                        ProvenInference::compatibility_right()
                            .specialize(&substitutions!(A: a, B: b, C: l)),
                    )
                    .unwrap(),
                );
            }
        }

        None
    }

    pub fn unfold_up_to_n_subformulas_proof(&self, n: usize) -> ProofWithVariables {
        let mut proof = ProofWithVariables::eq_refl(self.clone());
        for _ in 0..n {
            let Some(new_proof) =
                proof.conclusion().as_eq_sides().unwrap()[1].unfold_any_one_subformula_proof()
            else {
                return proof;
            };
            proof = ProofWithVariables::eq_trans_chain(&[proof, new_proof]).unwrap();
        }
        proof
    }

    pub fn unfold_up_to_n_subformulas_equality_inference(&self, n: usize) -> ProvenInference {
        let mut inference = ProvenInference::eq_refl(self);
        for _ in 0..n {
            let Some(new_inference) = inference
                .conclusion
                .unfold_any_one_subformula_equality_inference()
            else {
                return inference;
            };
            let [_a, b] = new_inference.conclusion.as_eq_sides().unwrap();
            inference = ProvenInference::derive_chain(
                "eq_trans",
                vec![inference, new_inference],
                &ic!(self = b).to_rwm(),
            )
            .unwrap();
        }
        inference
    }
    // pub fn unfold_left(&mut self, levels_deduction_available_under: u32) -> bool {
    //     if self.unfold_here() {
    //         return true;
    //     }
    //     match_ic!(self, {
    //         ((implies l) r) => {
    //             if let Some(less) = levels_deduction_available_under.checked_sub(1) {
    //                 let mut l = l.clone();
    //                 let mut r = r.clone();
    //                 if l.unfold_left(less) || r.unfold_left(less) {
    //                     *self = ic!((implies l) r);
    //                     return true
    //                 }
    //             }
    //         },
    //         ((and l) r) => {
    //             let mut l = l.clone();
    //             let mut r = r.clone();
    //             if l.unfold_left(levels_deduction_available_under) || r.unfold_left(levels_deduction_available_under) {
    //                 *self = ic!((and l) r);
    //                 return true
    //             }
    //         },
    //         (all r) => {
    //             let mut r = r.clone();
    //             if r.unfold_left(levels_deduction_available_under) {
    //                 *self = ic!(all r);
    //                 return true
    //             }
    //         },
    //         (l r) => {
    //             let mut l = l.clone();
    //             if l.unfold_left(levels_deduction_available_under) {
    //                 *self = ic!(l r.clone());
    //                 return true
    //             }
    //         },
    //     });
    //     false
    // }
    pub fn unfold_many(&mut self) -> usize {
        // self.children_mut()
        //     .into_iter()
        //     .map(|c| c.unfold_many())
        //     .sum::<usize>()
        //     + self.unfold_here() as usize
        let mut result = self.unfold_here() as usize;
        *self = self.map_children_rwm(|c| {
            let mut c = c.clone();
            result += c.unfold_many();
            c
        });
        result
    }
    pub fn unfold_until(&mut self, max: usize) {
        let mut total = 0;
        loop {
            let n = self.unfold_many();
            total += n;
            if n == 0 || total > max {
                return;
            }
        }
    }

    // pub fn fancy_unfold_here(&self) -> Option<FancyUnfoldResults> {
    //     match_ic!(self, {
    //         ((const a) b) => {Some(TrueFormula::definition_of_const(a.clone(), b.clone())) },
    //         (((fuse a) b) c) => {Some(TrueFormula::definition_of_fuse(a.clone(),b.clone(), c.clone())) },
    //         ((name => body) argument) => Some(fancy_unfold_lambda(name, body, argument, self)),
    //         _ => None,
    //     })
    // }
}

impl ProvenInference {
    pub fn fold_equivalence(a: RWMFormula, b: RWMFormula) -> Option<ProvenInference> {
        let ap = a.unfold_up_to_n_subformulas_equality_inference(100);
        let bp = b.unfold_up_to_n_subformulas_equality_inference(100);
        ProvenInference::eq_trans_chain(&[ap, bp.flip_conclusion()]).ok()
    }
}

// pub struct FancyUnfoldResults {
//     pub new_formula: Formula,
//     pub certificate: TrueFormula,
// }
//
// /// assumes `body` is a pretty formula with `Metavariable`s for variable_name, not combinators, and has no free variables
// /// raw_form is of (variable_name => body)
// /// returns (raw_form argument) = (body[variable_name:=argument]).raw at same position
// fn fancy_unfold_lambda(
//     variable_name: &str,
//     body: &Formula,
//     argument: &Formula,
//     raw_form: &Formula,
// ) -> Option<FancyUnfoldResults> {
//     if !body.contains_free_metavariable(variable_name) {
//         return match_ic!(raw_form, {
//             (const b) => Some(TrueFormula::definition_of_const(b.clone(), argument.clone())),
//             _ =>  None,
//         });
//     }
//     match &body.value {
//         FormulaValue::Atom(_) => {}
//         FormulaValue::Apply(children) => {
//             let raw_children = match_ic!(raw_form, {
//                 ((fuse l) r) => [l, r],
//                 _ => {
//                     // We should only reach this case if the `fuse` was elided (`fuse (const foo) id` reduced to `foo`)
//                     let result = body.with_metavariable_replaced(variable_name, argument);
//                     return TrueFormula::eq_refl(ic!(raw_form argument))
//                 }
//             });
//             let unfoldings = children
//                 .iter()
//                 .zip(raw_children)
//                 .map(|(c, r)| fancy_unfold_lambda(variable_name, c, argument, r))
//                 .collect::<Option<[FancyUnfoldResults; 2]>>()?;
//             // let new_forms = unfoldings.map(|u| u.as_eq_sides().unwrap()[1]);
//
//             let c1_raw_form_arg_equals_fused = TrueFormula::definition_of_fuse(raw_children[0].clone(), raw_children[1].clone(), argument.clone());
//             let acbc_equals_ebc = TrueFormula::compatibility_left(&unfoldings[0], ic!({raw_children[1]} argument));
//             let acbc_equals_ebc = TrueFormula::compatibility_left(&unfoldings[0], ic!({raw_children[1]} argument));
//             let c2_c1_equals_
//         }
//         FormulaValue::And(_) => {}
//         FormulaValue::Equals(_) => {}
//         FormulaValue::Implies(_) => {}
//         FormulaValue::NamedGlobal { .. } => {}
//         FormulaValue::Metavariable(v2) => {
//             assert_eq!(v2, variable_name, "shouldn't reach this case");
//         }
//         FormulaValue::NameAbstraction(_, _, _) => {}
//     }
//     match_ic!(body, {
//         {
//             Formula::metavariable(variable_name.to_string())
//         }
//     })
// }

// ///
// fn equivalence_search(a: &Formula, b: &Formula) -> Result<Inference, String> {
//     if premises.len() != 1 {
//         return Err("Unfolding must have exactly 1 premise".to_string());
//     }
//
//     match (
//         &premises[0].as_raw_with_metavariables().value,
//         &conclusion.as_raw_with_metavariables().value,
//     ) {}
// }

// pub struct DeriveFoldEquivalence {
//     max_depth: usize,
// }
// impl Default for DeriveFoldEquivalence {
//     fn default() -> Self {
//         DeriveFoldEquivalence { max_depth: 100 }
//     }
// }
// impl Deriver for DeriveFoldEquivalence {
//     fn try_derive(&self, premises: &[&Formula], conclusion: &Formula) -> Result<Inference, String> {
//         let Some([a, b]) = conclusion.as_raw_with_metavariables().as_eq_sides() else {
//             return Err(format!(
//                 "fold-equivalence requires `=` conclusion, but got {}",
//                 conclusion
//             ));
//         };
//
//         if a == b {
//             return Ok(get_deriver_by_name("eq_refl")
//                 .try_derive(&[], conclusion)
//                 .unwrap());
//         }
//         if self.max_depth == 0 {
//             return Err("max depth exceeded in DeriveFoldEquivalence".to_string());
//         }
//         match (&a.value, &b.value) {
//             (FormulaValue::Apply(a), FormulaValue::Apply(b)) => {
//                 todo!()
//             }
//             (FormulaValue::Apply(a), b) => {
//                 // match_ic!(a, {
//                 //     ((const a) _b) => {*self = a.clone(); true },
//                 //     (((fuse a) b) c) => {*self = ic!((a c)(b c)); true },
//                 //     _ => false,
//                 // })
//                 todo!()
//             }
//             (a, FormulaValue::Apply(b)) => {
//                 todo!()
//             }
//             (a, b) => return Err("incompatible sides for DeriveFoldEquivalence".to_string()),
//         }
//     }
// }
//
// pub struct DeriveByUnfolding;
// impl Deriver for DeriveByUnfolding {
//     fn try_derive(&self, premises: &[&Formula], conclusion: &Formula) -> Result<Inference, String> {
//         if premises.len() != 1 {
//             return Err("Unfolding must have exactly 1 premise".to_string());
//         }
//
//         let premise = premises[0];
//         let equivalence_statement = ic!(premise = conclusion);
//         let equivalence_inference =
//             DeriveFoldEquivalence::default().try_derive(premises, &equivalence_statement)?;
//         let conclusion_provider = DeriveBySpecializing(Inference::substitute_whole_formula())
//             .try_derive(&[&equivalence_statement, premise], conclusion)
//             .unwrap();
//         let premises: Vec<Formula> = premises.iter().copied().cloned().collect();
//         Ok(Inference::chain(
//             premises.clone(),
//             vec![equivalence_inference, Inference::premise(premises, 0)],
//             conclusion_provider,
//         )
//         .unwrap())
//     }
// }
