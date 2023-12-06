use crate::introspective_calculus::proof_hierarchy::{
    ProofWithPremises, ProofWithVariables, Proven,
};
use crate::introspective_calculus::{
    Atom, Formula, FormulaValue, RWMFormula, RWMFormulaValue, RawFormula, RawFormulaValue,
    ToFormula,
};
use crate::utils::todo;
use crate::{formula, ic};
use clap::arg;
use hash_capsule::HashCapsule;
use itertools::Itertools;
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::io::ErrorKind::ArgumentListTooLong;
use std::iter::zip;
use std::ops::Deref;
use std::sync::Arc;

// convenient form of: pair-chain
pub enum ArgumentList {
    Nil,
    Cons(RawFormula, Arc<ArgumentList>),
}

// impl ArgumentList {
//     pub fn head(&self) -> RawFormula {}
//     pub fn tail(&self) -> ArgumentList {}
// }

// convenient form of: UncurriedFunction that returns a pair-chain
pub enum GeneralizedArgumentList {
    Nil,
    Cons(UncurriedFunction, Arc<GeneralizedArgumentList>),
}

// impl GeneralizedArgumentList {
//     pub fn head(&self) -> UncurriedFunction {}
//     pub fn tail(&self) -> GeneralizedArgumentList {}
// }

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct UncurriedFunction(HashCapsule<UncurriedFunctionInner>);
impl Deref for UncurriedFunction {
    type Target = UncurriedFunctionInner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl Default for UncurriedFunction {
    fn default() -> Self {
        UncurriedFunctionValue::Constant(Default::default()).into()
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct UncurriedFunctionInner {
    value: UncurriedFunctionValue,
    formula_cache: RawFormula,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum UncurriedFunctionValue {
    Constant(RawFormula),
    Apply([UncurriedFunction; 2]),
    PopIn(UncurriedFunction),
    Top,
}
impl From<UncurriedFunctionValue> for UncurriedFunction {
    fn from(value: UncurriedFunctionValue) -> Self {
        UncurriedFunction::new(value)
    }
}
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct UncurriedFunctionEquivalence {
    pub sides: [UncurriedFunction; 2],
}

impl UncurriedFunctionEquivalence {
    pub fn formula(&self) -> RawFormula {
        let [a, b] = self.sides.each_ref().map(|s| s.formula());
        ic!(a = b).already_raw().unwrap()
    }
}

impl Proven<UncurriedFunctionEquivalence> {
    pub fn refl(value: UncurriedFunction) -> Self {
        Proven::new(
            UncurriedFunctionEquivalence {
                sides: [value.clone(), value.clone()],
            },
            ProofWithVariables::eq_refl(value.formula().into()),
        )
    }
    pub fn trans_chain(
        steps: &[Proven<UncurriedFunctionEquivalence>],
    ) -> Result<Proven<UncurriedFunctionEquivalence>, String> {
        Ok(Proven::new(
            UncurriedFunctionEquivalence {
                sides: [
                    steps[0].formula().sides[0].clone(),
                    steps.last().unwrap().formula().sides[1].clone(),
                ],
            },
            ProofWithVariables::eq_trans_chain(
                &steps.iter().map(|step| step.proof().clone()).collect_vec(),
            )?,
        ))
    }
}

impl UncurriedFunction {
    pub fn value(&self) -> &UncurriedFunctionValue {
        &self.value
    }
    pub fn formula(&self) -> RawFormula {
        self.formula_cache.clone()
    }

    pub fn new(value: UncurriedFunctionValue) -> Self {
        let formula_cache = match &value {
            UncurriedFunctionValue::Constant(f) => ic!(const f).already_raw().unwrap(),
            UncurriedFunctionValue::Apply(children) => {
                let [a, b] = children.each_ref().map(|c| c.formula().to_formula());
                ic!((fuse a) b).already_raw().unwrap()
            }
            UncurriedFunctionValue::PopIn(child) => {
                ic!(((const { child.formula() }),)).already_raw().unwrap()
            }
            UncurriedFunctionValue::Top => ic!((const,)).already_raw().unwrap(),
        };
        UncurriedFunction(HashCapsule::new(UncurriedFunctionInner {
            value,
            formula_cache,
        }))
    }

    pub fn args_to_return(&self, goal: &RawFormula) -> Result<ArgumentList, String> {
        let mut args = Vec::new();
        self.add_args_to_return(goal, 0, &mut args)?;
        let mut result = ArgumentList::Nil;
        for argument in args.into_iter().rev() {
            result = ArgumentList::Cons(argument.unwrap_or_default(), Arc::new(result));
        }
        let test_call = self.call(&result);
        assert_eq!(test_call.sides[1], *goal);
        Ok(result)
    }
    pub fn add_args_to_return(
        &self,
        goal: &RawFormula,
        skipped: usize,
        collector: &mut Vec<Option<RawFormula>>,
    ) -> Result<(), String> {
        match (self.value(), goal.value()) {
            (UncurriedFunctionValue::Constant(f), _) => {
                if f != goal {
                    return Err(format!(
                        "Tried to unify formulas with conflicting constants: `{f} := {goal}`"
                    ));
                }
            }
            (UncurriedFunctionValue::Apply(children), RawFormulaValue::Apply(goal_children)) => {
                for (child, goal_child) in zip(children, goal_children) {
                    child.add_args_to_return(&goal_child, skipped, collector)?;
                }
            }
            (UncurriedFunctionValue::PopIn(child), _) => {
                child.add_args_to_return(goal, skipped + 1, collector)?;
            }
            (UncurriedFunctionValue::Top, _) => {
                while collector.len() <= skipped {
                    collector.push(None);
                }
                match &collector[skipped] {
                    None => collector[skipped] = Some(goal.clone()),
                    Some(existing) => {
                        if existing != goal {
                            return Err(format!("Variable `{skipped}`, which was already assigned value `{existing}`, also needs conflicting value `{goal}`"));
                        }
                    }
                }
            }
            _ => return Err(format!("Could not unify `{self}` with `{goal}`")),
        }
        Ok(())
    }

    /// returns a proof of `self.formula (A,(B,(C,*))) = body[0:=A, 1:=B, 2:=C]`
    pub fn call(&self, arguments: &ArgumentList) -> Proven<UncurriedFunctionEquivalence> {
        let args = arguments.formula();
        match self.value() {
            UncurriedFunctionValue::Constant(f) => {
                // goal: (const f) args = f
                formula!("const f args = f", {f, args}).prove_by_rule()
            }
            UncurriedFunctionValue::Apply(children) => {
                // subgoal: (fuse A B) args = (A args) (B args)
                let [a, b] = children.each_ref().map(|child| child.formula());
                let f =
                    formula!("(fuse a b) args = (a args) (b args)", {a, b, args}).prove_by_rule();
                // subgoals: A args = A', B args = B'
                let child_proofs = children
                    .each_ref()
                    .map(|child| child.call(arguments.clone()));
                // goal: (fuse A B) args = A' B'
                let [ap, bp] = child_proofs.each_ref().map(|c| c.sides[1].clone());
                formula!("(fuse a b) args = ap bp", {a, b, ap, bp, args})
                    .prove_by_substitution_with(&child_proofs)
            }
            UncurriedFunctionValue::PopIn(child) => {
                // subgoal: (const P,)(head, tail) = P tail
                let p = child.formula();
                let ArgumentList::Cons(head, tail) = arguments else {
                    panic!("insufficient arguments passed to call")
                };
                let a = formula!("(const p,)(head, tail) = p tail", {p, head, tail})
                    .prove_by_unfolding();
                // subgoal: P tail = P'
                let b = child.call(tail);
                // goal: (const P,)(head, tail) = P'
                Proven::<UncurriedFunctionEquivalence>::trans_chain(&[a, b]).unwrap()
            }
            UncurriedFunctionValue::Top => {
                // goal: (const,)(head, tail) = head
                let ArgumentList::Cons(head, tail) = arguments else {
                    panic!("insufficient arguments passed to call")
                };
                formula!("(const,)(head, tail) = head", {p, head, tail}).prove_by_unfolding()
            }
        }
    }

    pub fn generalized_args_to_return(
        &self,
        goal: &UncurriedFunction,
    ) -> Result<GeneralizedArgumentList, String> {
        let mut args = Vec::new();
        self.add_generalized_args_to_return(goal, 0, &mut args)?;
        let mut result = GeneralizedArgumentList::Nil;
        for argument in args.into_iter().rev() {
            result = GeneralizedArgumentList::Cons(argument.unwrap_or_default(), Arc::new(result));
        }
        let test_call = self.generalized_call(&result);
        assert_eq!(test_call.sides[1], *goal);
        Ok(result)
    }
    pub fn add_generalized_args_to_return(
        &self,
        goal: &UncurriedFunction,
        skipped: usize,
        collector: &mut Vec<Option<UncurriedFunction>>,
    ) -> Result<(), String> {
        match (self.value(), goal.value()) {
            (UncurriedFunctionValue::Constant(f), UncurriedFunctionValue::Constant(g)) => {
                if f != g {
                    return Err(format!(
                        "Tried to unify formulas with conflicting constants: `{f} := {g}`"
                    ));
                }
            }
            (
                UncurriedFunctionValue::Apply(children),
                UncurriedFunctionValue::Apply(goal_children),
            ) => {
                for (child, goal_child) in zip(children, goal_children) {
                    child.add_generalized_args_to_return(&goal_child, skipped, collector)?;
                }
            }
            (UncurriedFunctionValue::PopIn(child), _) => {
                child.add_generalized_args_to_return(goal, skipped + 1, collector)?;
            }
            (UncurriedFunctionValue::Top, _) => {
                while collector.len() <= skipped {
                    collector.push(None);
                }
                match &collector[skipped] {
                    None => collector[skipped] = Some(goal.clone()),
                    Some(existing) => {
                        if existing != goal {
                            return Err(format!("Variable `{skipped}`, which was already assigned value `{existing}`, also needs conflicting value `{goal}`"));
                        }
                    }
                }
            }
            _ => return Err(format!("Could not unify `{self}` with `{goal}`")),
        }
        Ok(())
    }

    /// returns a proof of `(fuse (const self.formula) args.formula) = self[0:=A, 1:=B, 2:=C]`
    pub fn generalized_call(
        &self,
        arguments: &GeneralizedArgumentList,
    ) -> Proven<UncurriedFunctionEquivalence> {
        let args = arguments.uncurried_function().formula();
        match self.value() {
            UncurriedFunctionValue::Constant(f) => {
                // goal: fuse (const (const f)) args = (const f)
                formula!("(fuse (const (const f)) args) = (const f)", {f, args})
                    .prove_by_specializing_axiom()
            }
            UncurriedFunctionValue::Apply(children) => {
                // subgoal: fuse (const (fuse A B)) args = fuse (fuse (const A) args) (fuse (const B) args)
                let [a, b] = children.each_ref().map(|child| child.formula());
                let f = formula!("fuse (const (fuse a b)) args = fuse (fuse (const a) args) (fuse (const b) args)", {a, b, args}).prove_by_specializing_axiom();
                // subgoals: fuse (const A) args = A', fuse (const B) args = B'
                let child_proofs = children
                    .each_ref()
                    .map(|child| child.generalized_call(arguments));
                // goal: fuse (const (fuse A B)) args = fuse A' B'
                let combined: UncurriedFunction = UncurriedFunctionValue::Apply(
                    child_proofs.each_ref().map(|c| c.sides[1].clone()),
                )
                .into();
                let g = formula!("(fuse a b) args = apbp", {a, b, args, apbp: combined.formula()})
                    .prove_by_substitution_with(&child_proofs);
                // canonicalize if children are both PopIn or both Constant
                let e = combined.canonicalize_locally();

                Proven::<UncurriedFunctionEquivalence>::trans_chain(&[g, e]).unwrap()
            }
            UncurriedFunctionValue::PopIn(child) => {
                // subgoal: fuse (const (const P,)) (l => (head l, tail l)) = fuse (const P) tail
                let p = child.formula();
                let GeneralizedArgumentList::Cons(head, tail) = arguments else {
                    panic!("insufficient arguments passed to call")
                };
                let head = head.formula();
                let a = formula!("fuse (const (const p,)) (l => (head l, tail l)) = fuse (const p) tail", {p, head, tail: tail.uncurried_function().formula()})
                    .prove_by_specializing_axiom();
                // subgoal: fuse (const P) tail = P'
                let b = child.generalized_call(tail);
                // goal: fuse (const (const P,)) (l => (head l, tail l)) = P'
                Proven::<UncurriedFunctionEquivalence>::trans_chain(&[a, b]).unwrap()
            }
            UncurriedFunctionValue::Top => {
                // goal: fuse (const (const,)) (l => (head l, tail l)) = head
                let GeneralizedArgumentList::Cons(head, tail) = arguments else {
                    panic!("insufficient arguments passed to call")
                };
                formula!("fuse (const (const,)) (l => (head l, tail l)) = head", {head, tail})
                    .prove_by_specializing_axiom()
            }
        }
    }
    pub fn canonicalize_locally(&self) -> Proven<UncurriedFunctionEquivalence> {
        if let UncurriedFunctionValue::Apply([a, b]) = self.value() {
            match (a.value(), b.value()) {
                (UncurriedFunctionValue::Constant(a), UncurriedFunctionValue::Constant(b)) => {
                    let combined = ic!(a b).already_raw().unwrap();
                    return Proven::new(
                        UncurriedFunctionEquivalence {
                            sides: [
                                self.clone(),
                                UncurriedFunctionValue::Constant(combined).into(),
                            ],
                        },
                        // goal: fuse (const a) (const b) = const (a b)
                        formula!("fuse (const a) (const b) = const (a b)", {a, b})
                            .prove_by_specializing_axiom(),
                    );
                }
                // (UncurriedFunctionValue::PopIn(a), UncurriedFunctionValue::PopIn(b)) => {
                //     let combined = UncurriedFunctionValue::PopIn(
                //         UncurriedFunctionValue::Apply([a.clone(), b.clone()]).into(),
                //     )
                //     .into();
                //
                //     UncurriedFunctionEquivalence {
                //         sides: [self.clone(), combined],
                //         // goal: fuse (const a,) (const b,) = (const (fuse a b),)
                //         // note: only equivalent if the next arg is known to be of the form (x,y)! (or maybe if a,b known to be UFs?)
                //         proof: Proof,
                //     }
                // }
                _ => (),
            }
        }
        Proven::<UncurriedFunctionEquivalence>::refl(self.clone())
    }
}

impl ArgumentList {
    pub fn formula(&self) -> RawFormula {
        match self {
            ArgumentList::Cons(head, tail) => {
                let tail = tail.formula();
                ic!((head, tail)).already_raw().unwrap()
            }
            ArgumentList::Nil => {
                // anything is fine
                RawFormula::default()
            }
        }
    }
}

impl GeneralizedArgumentList {
    pub fn uncurried_function(&self) -> UncurriedFunction {
        match self {
            GeneralizedArgumentList::Cons(head, tail) => {
                let tail = tail.uncurried_function();
                // x => (head x, tail x)
                // = x => y => y (head x) (tail x)
                // = x => (fuse (fuse id (const (head x))) (const (tail x)))
                // = fusetree["fuse" ("fuse id" (fuse (const const) head)) (fuse (const const) tail)]
                formula!("l => (head l, tail l)")
                    .to_rwm()
                    .with_metavariables_replaced_with_uncurried_functions(
                        &[
                            ("head".to_string(), head.clone()),
                            ("tail".to_string(), tail),
                        ]
                        .into_iter()
                        .collect(),
                    )
            }
            GeneralizedArgumentList::Nil => {
                // anything is fine
                UncurriedFunction::default()
            }
        }
    }
}

impl RWMFormula {
    pub fn with_metavariables_replaced_with_uncurried_functions(
        &self,
        substitutions: &BTreeMap<String, UncurriedFunction>,
    ) -> UncurriedFunction {
        if let Some(raw) = self.already_raw() {
            return UncurriedFunctionValue::Constant(raw).into();
        }
        match self.value() {
            RWMFormulaValue::Atom(_) => {
                unreachable!()
            }
            RWMFormulaValue::Apply(children) => UncurriedFunctionValue::Apply(
                children
                    .map(|c| c.with_metavariables_replaced_with_uncurried_functions(substitutions)),
            )
            .into(),
            RWMFormulaValue::Metavariable(name) => substitutions[&name].clone(),
        }
    }
    pub fn to_uncurried_function_of(&self, arguments: &[String]) -> UncurriedFunction {
        // let Some((head, tail)) = arguments.split_first() else {
        //     return UncurriedFunctionValue::Constant(self.already_raw().unwrap()).into();
        // };
        if let Some(already_raw) = self.already_raw() {
            return UncurriedFunctionValue::Constant(already_raw).into();
        }
        // if !self.contains_free_metavariable(head) {
        //     return UncurriedFunctionValue::PopIn(self.to_uncurried_function_of(tail)).into();
        // }
        match self.value() {
            RWMFormulaValue::Atom(_) => {
                unreachable!()
            }
            RWMFormulaValue::Apply(children) => UncurriedFunctionValue::Apply(
                children.map(|c| c.to_uncurried_function_of(arguments)),
            )
            .into(),
            RWMFormulaValue::Metavariable(name) => {
                // assert_eq!(name, head);
                let Some((head, tail)) = arguments.split_first() else {
                    panic!("didn't include all metaveriables in to_uncurried_function_of")
                };
                if name == *head {
                    UncurriedFunctionValue::Top.into()
                } else {
                    UncurriedFunctionValue::PopIn(self.to_uncurried_function_of(tail)).into()
                }
            }
        }
    }
}
