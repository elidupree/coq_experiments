use crate::ic;
use crate::introspective_calculus::proof_hierarchy::Proof;
use crate::introspective_calculus::{
    Atom, Formula, RWMFormula, RWMFormulaValue, RawFormula, ToFormula,
};
use crate::utils::todo;
use hash_capsule::HashCapsule;
use itertools::Itertools;
use std::ops::Deref;

// convenient form of: pair-chain
pub struct ArgumentList {}

impl ArgumentList {
    pub fn head(&self) -> RawFormula {}
    pub fn tail(&self) -> ArgumentList {}
}

// convenient form of: UncurriedFunction that returns a pair-chain
pub struct GeneralizedArgumentList {}

impl GeneralizedArgumentList {
    pub fn head(&self) -> UncurriedFunction {}
    pub fn tail(&self) -> GeneralizedArgumentList {}
}

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
pub struct UncurriedFunctionEquivalence {
    sides: [UncurriedFunction; 2],
}

impl UncurriedFunctionEquivalence {
    pub fn trans_chain(steps: &[UncurriedFunctionEquivalence]) -> UncurriedFunctionEquivalence {
        UncurriedFunctionEquivalence {
            sides: [
                steps[0].sides[0].clone(),
                steps.last().unwrap().sides[1].clone(),
            ],
            proof: Proof::eq_trans_chain(
                &steps.iter().map(|step| step.proof.clone()).collect_vec(),
            ),
        }
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

    pub fn args_to_return(&self, retval: RawFormula) -> Result<ArgumentList, String> {}

    /// returns a proof of `self.formula (A,(B,(C,*))) = body[0:=A, 1:=B, 2:=C]`
    pub fn call(&self, arguments: ArgumentList) -> Proof {
        match self.value() {
            UncurriedFunctionValue::Constant(f) => {
                // goal: (const f) args = f
                todo(())
            }
            UncurriedFunctionValue::Apply(children) => {
                // subgoal: (fuse A B) args = (A args) (B args)
                let f = todo();
                // subgoals: A args = A', B args = B'
                let [a, b] = children
                    .each_ref()
                    .map(|child| child.call(arguments.clone()));
                // goal: (fuse A B) args = A' B'
                todo((a, b, f))
            }
            UncurriedFunctionValue::PopIn(child) => {
                // subgoal: (const P,)(head, tail) = P tail
                let a = todo(());
                // subgoal: P tail = P'
                let b = child.call(arguments.tail());
                // goal: (const P,)(head, tail) = P'
                Proof::eq_trans(&[a, b])
            }
            UncurriedFunctionValue::Top => {
                // goal: (const,)(head, tail) = head
                todo(())
            }
        }
    }

    pub fn generalized_args_to_return(
        &self,
        retval: UncurriedFunction,
    ) -> Result<GeneralizedArgumentList, String> {
    }

    /// returns a proof of `(fuse (const self.formula) args.formula) = self[0:=A, 1:=B, 2:=C]`
    pub fn generalized_call(
        &self,
        arguments: GeneralizedArgumentList,
    ) -> UncurriedFunctionEquivalence {
        match self.value() {
            UncurriedFunctionValue::Constant(f) => {
                // goal: x => (const (const f)) args = (const f)
                todo(())
            }
            UncurriedFunctionValue::Apply(children) => {
                // subgoal: fuse (const (fuse A B)) args = fuse (fuse (const A) args) (fuse (const B) args)
                let f = todo();
                // subgoals: fuse (const A) args = A', fuse (const B) args = B'
                let [a, b] = children
                    .each_ref()
                    .map(|child| child.generalized_call(arguments.clone()));
                // goal: fuse (const (fuse A B)) args = fuse A' B'
                todo((a, b, f))
                // canonicalize if children are both PopIn or both Constant
            }
            UncurriedFunctionValue::PopIn(child) => {
                // subgoal: fuse (const (const P,)) (l => (head l, tail l)) = fuse (const P) tail
                let a = todo(());
                // subgoal: fuse (const P) tail = P'
                let b = child.generalized_call(arguments.tail());
                // goal: fuse (const (const P,)) (l => (head l, tail l)) = P'
                Proof::eq_trans(&[a, b])
            }
            UncurriedFunctionValue::Top => {
                // goal: fuse (const (const,)) (l => (head l, tail l)) = head
                todo(())
            }
        }
    }
    pub fn canonicalize_locally(&self) -> UncurriedFunctionEquivalence {
        if let UncurriedFunctionValue::Apply([a, b]) = self.value() {
            match (a.value(), b.value()) {
                (UncurriedFunctionValue::Constant(a), UncurriedFunctionValue::Constant(b)) => {
                    let combined = ic!(a b).already_raw().unwrap();
                    UncurriedFunctionEquivalence {
                        sides: [
                            self.clone(),
                            UncurriedFunctionValue::Constant(combined).into(),
                        ],
                        // goal: fuse (const a) (const b) = const (a b)
                        proof: Proof,
                    }
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
                _ => UncurriedFunctionEquivalence {
                    sides: [self.clone(), self.clone()],
                    proof: Proof::eq_refl(),
                },
            }
        }
    }
}

impl GeneralizedArgumentList {
    pub fn uncurried_function(&self) -> UncurriedFunction {
        match self {
            Some((head, tail)) => {
                let tail = tail.uncurried_function();
                // x => (head x, tail x)
                // = x => y => y (head x) (tail x)
                // = x => (fuse (fuse id (const (head x))) (const (tail x)))
                // = fusetree["fuse" ("fuse id" (fuse (const const) head)) (fuse (const const) tail)]
                ic!("l" => ("head" "l", "tail" "l")).to_rwm()
            }
            None => {
                // anything is fine
                UncurriedFunction::default()
            }
        }
    }
}

impl RWMFormula {
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
            RWMFormulaValue::Apply(children) => {
                UncurriedFunctionValue::Apply(children.map(RWMFormula::to_uncurried_function_of))
                    .into()
            }
            RWMFormulaValue::Metavariable(name) => {
                // assert_eq!(name, head);
                let Some((head, tail)) = arguments.split_first() else {
                    panic!("didn't include all metaveriables in to_uncurried_function_of")
                };
                if name == head {
                    UncurriedFunctionValue::Top.into()
                } else {
                    UncurriedFunctionValue::PopIn(self.to_uncurried_function_of(tail)).into()
                }
            }
        }
    }
}
