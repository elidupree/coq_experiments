use crate::introspective_calculus::proof_hierarchy::{Proof, Proven};
use crate::introspective_calculus::provers::{
    ByAxiomSchema, BySpecializingAxiom, BySubstitutingWith, ByUnfolding, FormulaProver,
};
use crate::introspective_calculus::{Formula, RWMFormula, RWMFormulaValue, RawFormula, ToFormula};
use crate::{formula, ic};
use hash_capsule::HashCapsule;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::iter::zip;
use std::ops::Deref;
use std::sync::Arc;

// convenient form of: pair-chain
#[derive(Debug)]
pub enum PairChain {
    Nil,
    Cons(RWMFormula, Arc<PairChain>),
}

impl FromIterator<RWMFormula> for PairChain {
    fn from_iter<T: IntoIterator<Item = RWMFormula>>(iter: T) -> Self {
        let mut iter = iter.into_iter();
        match iter.next() {
            None => PairChain::Nil,
            Some(f) => PairChain::Cons(f, Arc::new(iter.collect())),
        }
    }
}

// impl ArgumentList {
//     pub fn head(&self) -> RawFormula {}
//     pub fn tail(&self) -> ArgumentList {}
// }

// convenient form of: UncurriedFunction that returns a pair-chain
#[derive(Debug)]
pub enum UncurriedPairChain {
    Nil,
    Cons(UncurriedFunction, Arc<UncurriedPairChain>),
}

impl FromIterator<UncurriedFunction> for UncurriedPairChain {
    fn from_iter<T: IntoIterator<Item = UncurriedFunction>>(iter: T) -> Self {
        let mut iter = iter.into_iter();
        match iter.next() {
            None => UncurriedPairChain::Nil,
            Some(f) => UncurriedPairChain::Cons(f, Arc::new(iter.collect())),
        }
    }
}

// impl GeneralizedArgumentList {
//     pub fn head(&self) -> UncurriedFunction {}
//     pub fn tail(&self) -> GeneralizedArgumentList {}
// }

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, Serialize, Deserialize)]
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

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, Serialize, Deserialize)]
pub struct UncurriedFunctionInner {
    value: UncurriedFunctionValue,
    formula_cache: RawFormula,
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, Serialize, Deserialize)]
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
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, Serialize, Deserialize)]
pub struct UncurriedFunctionEquivalence {
    pub sides: [UncurriedFunction; 2],
}

impl ToFormula for UncurriedFunctionEquivalence {
    fn to_formula(&self) -> Formula {
        self.formula().to_formula()
    }
}

impl UncurriedFunctionEquivalence {
    pub fn formula(&self) -> RawFormula {
        let [a, b] = self.sides.each_ref().map(|s| s.formula());
        ic!(a = b).to_raw().unwrap()
    }
    pub fn prove(&self, prover: impl FormulaProver) -> Proven<Self> {
        Proven::new(self.clone(), self.formula().prove(prover))
    }
    pub fn args_to_return(&self, goal: &RWMFormula) -> Result<PairChain, String> {
        let [a, b] = goal.as_eq_sides().unwrap();
        let mut args = Vec::new();
        self.sides[0].add_args_to_return(&a, 0, &mut args)?;
        self.sides[1].add_args_to_return(&b, 0, &mut args)?;
        self.sides[0].finish_args_to_return(&a, args.clone());
        Ok(self.sides[1].finish_args_to_return(&b, args))
    }
    pub fn generalized_args_to_return(
        &self,
        goal: &UncurriedFunctionEquivalence,
    ) -> Result<UncurriedPairChain, String> {
        let [a, b] = goal.sides.clone();
        let mut args = Vec::new();
        self.sides[0].add_generalized_args_to_return(&a, 0, &mut args)?;
        self.sides[1].add_generalized_args_to_return(&b, 0, &mut args)?;
        self.sides[0].finish_generalized_args_to_return(&a, args.clone());
        Ok(self.sides[1].finish_generalized_args_to_return(&b, args))
    }
}

impl Proven<UncurriedFunctionEquivalence> {
    pub fn refl(value: UncurriedFunction) -> Self {
        Proven::new(
            UncurriedFunctionEquivalence {
                sides: [value.clone(), value.clone()],
            },
            Proof::eq_refl(value.formula().into()),
        )
    }
    pub fn flip(&self) -> Self {
        Proven::new(
            UncurriedFunctionEquivalence {
                sides: [self.sides[1].clone(), self.sides[0].clone()],
            },
            self.proof().flip_conclusion(),
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
            Proof::eq_trans_chain(&steps.iter().map(|step| step.proof().clone()).collect_vec())?,
        ))
    }
    pub fn specialize(&self, args: &PairChain) -> Proof {
        let [pl, pr] = self.sides.each_ref().map(|s| s.call(args));
        let pm = ic!(
            ({self.sides[0].formula()} {args.formula()}) =
            ({self.sides[1].formula()} {args.formula()})
        )
        .prove(BySubstitutingWith(&[self.proof().clone()]));
        Proof::eq_trans_chain(&[pl.flip_conclusion(), pm, pr]).unwrap()
    }
    pub fn partially_specialize(
        &self,
        args: &UncurriedPairChain,
    ) -> Proven<UncurriedFunctionEquivalence> {
        let [pl, pr] = self.sides.each_ref().map(|s| s.generalized_call(args));
        let pm = UncurriedFunctionEquivalence {
            sides: [pl.sides[0].clone(), pr.sides[0].clone()],
        }
        .prove(BySubstitutingWith(&[self.proof().clone()]));
        Self::trans_chain(&[pl.flip(), pm, pr]).unwrap()
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
                ic!(((const { child.formula() }),)).to_raw().unwrap()
            }
            UncurriedFunctionValue::Top => ic!((const,)).to_raw().unwrap(),
        };
        UncurriedFunction(HashCapsule::new(UncurriedFunctionInner {
            value,
            formula_cache,
        }))
    }
    pub fn constant(f: RawFormula) -> UncurriedFunction {
        UncurriedFunctionValue::Constant(f).into()
    }
    pub fn apply(children: [UncurriedFunction; 2]) -> UncurriedFunction {
        UncurriedFunctionValue::Apply(children).into()
    }
    pub fn pop_in(child: UncurriedFunction) -> UncurriedFunction {
        UncurriedFunctionValue::PopIn(child).into()
    }
    pub fn top() -> UncurriedFunction {
        UncurriedFunctionValue::Top.into()
    }
    pub fn nth_argument(n: usize) -> UncurriedFunction {
        match n.checked_sub(1) {
            None => UncurriedFunction::top(),
            Some(pred) => UncurriedFunction::pop_in(UncurriedFunction::nth_argument(pred)),
        }
    }

    pub fn args_to_return(&self, goal: &RWMFormula) -> Result<PairChain, String> {
        let mut args = Vec::new();
        self.add_args_to_return(goal, 0, &mut args)?;
        Ok(self.finish_args_to_return(goal, args))
    }
    pub fn finish_args_to_return(
        &self,
        goal: &RWMFormula,
        args: Vec<Option<RWMFormula>>,
    ) -> PairChain {
        let mut result = PairChain::Nil;
        for argument in args.into_iter().rev() {
            result = PairChain::Cons(argument.unwrap_or_default(), Arc::new(result));
        }
        let test_call = self.call(&result);
        assert_eq!(
            test_call.conclusion().as_eq_sides().unwrap()[1],
            goal.to_rwm(),
            "{} != {}",
            test_call.conclusion().as_eq_sides().unwrap()[1],
            goal.to_rwm(),
        );
        result
    }
    pub fn add_args_to_return(
        &self,
        goal: &RWMFormula,
        skipped: usize,
        collector: &mut Vec<Option<RWMFormula>>,
    ) -> Result<(), String> {
        match (self.value(), goal.value()) {
            (UncurriedFunctionValue::Constant(f), _) => {
                if &f.to_rwm() != goal {
                    return Err(format!(
                        "Tried to unify formulas with conflicting constants: `{f} := {goal}`"
                    ));
                }
            }
            (UncurriedFunctionValue::Apply(children), RWMFormulaValue::Apply(goal_children)) => {
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
    pub fn call(&self, arguments: &PairChain) -> Proof {
        let args = arguments.formula();
        let lhs = Formula::apply([self.formula().into(), args.into()]);
        match self.value() {
            UncurriedFunctionValue::Constant(f) => {
                // goal: (const f) args = f
                ic!(lhs = f).prove(ByAxiomSchema)
            }
            UncurriedFunctionValue::Apply(children) => {
                // subgoals: A args = A', B args = B'
                let child_proofs = children.each_ref().map(|child| child.call(arguments));
                let children_lhs = Formula::apply(
                    child_proofs
                        .each_ref()
                        .map(|c| c.conclusion().as_eq_sides().unwrap()[0].clone().into()),
                );
                let children_rhs = Formula::apply(
                    child_proofs
                        .each_ref()
                        .map(|c| c.conclusion().as_eq_sides().unwrap()[1].clone().into()),
                );
                let combined_child_result =
                    ic!(children_lhs = children_rhs).prove(BySubstitutingWith(&child_proofs));
                // subgoal: (fuse A B) args = (A args) (B args)
                let local_result = ic!(lhs = children_lhs).prove(ByAxiomSchema);
                // goal: (fuse A B) args = A' B'
                Proof::eq_trans_chain(&[local_result, combined_child_result]).unwrap()
            }
            UncurriedFunctionValue::PopIn(child) => {
                let PairChain::Cons(_head, tail) = arguments else {
                    panic!("insufficient arguments passed to call")
                };
                // subgoal: P tail = P'
                let child_result = child.call(tail);
                // subgoal: (const P,)(head, tail) = P tail
                let intermediate = child_result.conclusion().as_eq_sides().unwrap()[0].clone();
                let local_result = ic!(lhs = intermediate).prove(ByUnfolding);
                // goal: (const P,)(head, tail) = P'
                Proof::eq_trans_chain(&[local_result, child_result]).unwrap()
            }
            UncurriedFunctionValue::Top => {
                // goal: (const,)(head, tail) = head
                let PairChain::Cons(head, _tail) = arguments else {
                    panic!("insufficient arguments passed to call")
                };
                ic!(lhs = head).prove(ByUnfolding)
            }
        }
    }

    pub fn generalized_args_to_return(
        &self,
        goal: &UncurriedFunction,
    ) -> Result<UncurriedPairChain, String> {
        let mut args = Vec::new();
        self.add_generalized_args_to_return(goal, 0, &mut args)?;
        Ok(self.finish_generalized_args_to_return(goal, args))
    }
    pub fn finish_generalized_args_to_return(
        &self,
        goal: &UncurriedFunction,
        args: Vec<Option<UncurriedFunction>>,
    ) -> UncurriedPairChain {
        let mut result = UncurriedPairChain::Nil;
        for argument in args.into_iter().rev() {
            result = UncurriedPairChain::Cons(argument.unwrap_or_default(), Arc::new(result));
        }
        let test_call = self.generalized_call(&result);
        assert_eq!(test_call.sides[1], *goal);
        result
    }
    pub fn add_generalized_args_to_return(
        &self,
        goal: &UncurriedFunction,
        skipped: usize,
        collector: &mut Vec<Option<UncurriedFunction>>,
    ) -> Result<(), String> {
        //eprintln!("{}\n?:=\n{}\n", self, goal);
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
                    child.add_generalized_args_to_return(goal_child, skipped, collector)?;
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
        arguments: &UncurriedPairChain,
    ) -> Proven<UncurriedFunctionEquivalence> {
        let lhs = UncurriedFunction::apply([
            UncurriedFunction::constant(self.formula()),
            arguments.uncurried_function(),
        ]);
        // let args = arguments.uncurried_function().formula();
        match self.value() {
            UncurriedFunctionValue::Constant(f) => {
                // goal: fuse (const (const f)) args = (const f)
                let rhs = UncurriedFunction::constant(f.clone());
                UncurriedFunctionEquivalence { sides: [lhs, rhs] }.prove(BySpecializingAxiom)
            }
            UncurriedFunctionValue::Apply(children) => {
                // subgoals: fuse (const A) args = A', fuse (const B) args = B'
                let child_proofs = children
                    .each_ref()
                    .map(|child| child.generalized_call(arguments));
                let children_lhs =
                    UncurriedFunction::apply(child_proofs.each_ref().map(|c| c.sides[0].clone()));
                let children_rhs =
                    UncurriedFunction::apply(child_proofs.each_ref().map(|c| c.sides[1].clone()));
                let combined_child_results = UncurriedFunctionEquivalence {
                    sides: [children_lhs.clone(), children_rhs],
                }
                .prove(BySubstitutingWith(
                    &child_proofs.each_ref().map(|c| c.proof().clone()),
                ));
                // subgoal: fuse (const (fuse A B)) args = fuse (fuse (const A) args) (fuse (const B) args)
                let local_result = UncurriedFunctionEquivalence {
                    sides: [lhs, children_lhs],
                }
                .prove(BySpecializingAxiom);
                // goal: fuse (const (fuse A B)) args = fuse A' B'
                // canonicalize if children are both PopIn or both Constant
                let canonicalization = combined_child_results.sides[1].canonicalize_locally();

                Proven::<UncurriedFunctionEquivalence>::trans_chain(&[
                    local_result,
                    combined_child_results,
                    canonicalization,
                ])
                .unwrap()
            }
            UncurriedFunctionValue::PopIn(child) => {
                let UncurriedPairChain::Cons(_head, tail) = arguments else {
                    panic!("insufficient arguments passed to call")
                };
                // subgoal: fuse (const P) tail = P'
                let child_result = child.generalized_call(tail);
                // subgoal: fuse (const (const P,)) (l => (head l, tail l)) = fuse (const P) tail
                let local_result = UncurriedFunctionEquivalence {
                    sides: [lhs, child_result.sides[0].clone()],
                }
                .prove(BySpecializingAxiom);
                // goal: fuse (const (const P,)) (l => (head l, tail l)) = P'
                Proven::<UncurriedFunctionEquivalence>::trans_chain(&[local_result, child_result])
                    .unwrap()
            }
            UncurriedFunctionValue::Top => {
                // goal: fuse (const (const,)) (l => (head l, tail l)) = head
                let UncurriedPairChain::Cons(head, _tail) = arguments else {
                    panic!("insufficient arguments passed to call")
                };
                assert_eq!(
                    lhs.formula().to_rwm(),
                    formula!("fuse (const (const,)) (l => (head l, tail l))", {head:head.formula(), tail:_tail.uncurried_function().formula()}),
                    "{} !=",
                    lhs.formula(),
                );
                UncurriedFunctionEquivalence {
                    sides: [lhs, head.clone()],
                }
                .prove(BySpecializingAxiom)
            }
        }
    }
    pub fn canonicalize_locally(&self) -> Proven<UncurriedFunctionEquivalence> {
        if let UncurriedFunctionValue::Apply([a, b]) = self.value() {
            #[allow(clippy::single_match)]
            match (a.value(), b.value()) {
                (UncurriedFunctionValue::Constant(a), UncurriedFunctionValue::Constant(b)) => {
                    let combined = ic!(a b).already_raw().unwrap();
                    // goal: fuse (const a) (const b) = const (a b)
                    return UncurriedFunctionEquivalence {
                        sides: [self.clone(), UncurriedFunction::constant(combined)],
                    }
                    .prove(BySpecializingAxiom);
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

impl PairChain {
    pub fn formula(&self) -> RWMFormula {
        match self {
            PairChain::Cons(head, tail) => {
                let tail = tail.formula();
                ic!((head, tail)).to_rwm()
            }
            PairChain::Nil => {
                // anything is fine
                RWMFormula::default()
            }
        }
    }
}

impl UncurriedPairChain {
    pub fn uncurried_function(&self) -> UncurriedFunction {
        match self {
            UncurriedPairChain::Cons(head, tail) => {
                let tail = tail.uncurried_function();
                // x => (head x, tail x)
                // = x => y => y (head x) (tail x)
                // = x => (fuse (fuse id (const (head x))) (const (tail x)))
                // = fusetree["fuse" ("fuse id" (fuse (const const) head)) (fuse (const const) tail)]
                formula!("(head, tail)")
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
            UncurriedPairChain::Nil => {
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
        let result: UncurriedFunction = match self.value() {
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
        };
        // didn't work due to bootstrapping issues:
        // assert_eq!(
        //     result
        //         .call(
        //             &arguments
        //                 .iter()
        //                 .map(|arg| arg.to_formula().to_rwm())
        //                 .collect()
        //         )
        //         .conclusion()
        //         .as_eq_sides()
        //         .unwrap()[1],
        //     *self
        // );
        let test_args: PairChain = arguments
            .iter()
            .map(|arg| arg.to_formula().to_rwm())
            .collect();
        let mut test = ic!({result.formula()} {test_args.formula()}).to_rwm();
        test.unfold_until(1000);
        let mut test2 = self.clone();
        test2.unfold_until(100);
        assert_eq!(test, test2, "{test} != {test2}");
        result
    }
    pub fn already_uncurried_function(&self) -> Result<UncurriedFunction, String> {
        let result = if let Ok([a]) = ic!(const "a").matches::<[RWMFormula; 1]>(self) {
            Ok(UncurriedFunction::constant(
                a.to_raw()
                    .ok_or_else(|| format!("Not a UCF (not raw): {a}"))?,
            ))
        } else if let Ok([a]) = ic!(((const "a"),)).matches::<[RWMFormula; 1]>(self) {
            Ok(UncurriedFunction::pop_in(a.already_uncurried_function()?))
        } else if self == &ic!(const,).to_rwm() {
            Ok(UncurriedFunction::top())
        } else if let Ok([a, b]) = ic!((fuse "a") "b").matches::<[RWMFormula; 2]>(self) {
            Ok(UncurriedFunction::apply([
                a.already_uncurried_function()?,
                b.already_uncurried_function()?,
            ]))
        } else {
            Err(format!("Not an uncurried function: {self}"))
        };
        if let Ok(result) = &result {
            assert_eq!(self, &result.formula().to_rwm())
        }
        result
    }
    pub fn to_uncurried_function_equivalence(
        &self,
        arguments: &[String],
    ) -> Result<UncurriedFunctionEquivalence, String> {
        Ok(UncurriedFunctionEquivalence {
            sides: self
                .as_eq_sides()
                .ok_or_else(|| format!("Not an equivalence: {self}"))?
                .map(|s| s.to_uncurried_function_of(arguments)),
        })
    }
    pub fn already_uncurried_function_equivalence(
        &self,
    ) -> Result<UncurriedFunctionEquivalence, String> {
        Ok(UncurriedFunctionEquivalence {
            sides: self
                .as_eq_sides()
                .ok_or_else(|| format!("Not an equivalence: {self}"))?
                .try_map(|s| s.already_uncurried_function())?,
        })
    }
}
impl Proof {
    pub fn already_uncurried_function_equivalence(
        &self,
    ) -> Result<Proven<UncurriedFunctionEquivalence>, String> {
        Ok(Proven::new(
            self.conclusion().already_uncurried_function_equivalence()?,
            self.clone(),
        ))
    }
}
