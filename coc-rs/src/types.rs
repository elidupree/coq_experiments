use crate::term::{RecursiveTermKind, Term, TermKind, TermRef};
// use arrayvec::ArrayVec;
use std::iter;

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub enum TypeCheckResult {
    HasType(Term),
    NoType,
}

pub fn is_fully_reduced(term: TermRef) -> bool {
    use RecursiveTermKind::*;
    use TermKind::*;
    match term.kind() {
        Prop | Type | Variable(_) => true,
        Recursive(kind, children) => match kind {
            Lambda | ForAll => {
                is_fully_reduced(children[0].get().as_term_ref())
                    && is_fully_reduced(children[1].get().as_term_ref())
            }
            Apply => {
                is_fully_reduced(children[0].get().as_term_ref())
                    && is_fully_reduced(children[1].get().as_term_ref())
                    && !matches!(children[0].get().kind(), Recursive(Lambda, _))
            }
        },
    }
}

pub fn substitute_one(term: TermRef, replaced_index: u64, replacement: TermRef) -> Term {
    use RecursiveTermKind::*;
    use TermKind::*;
    match term.kind() {
        Prop => Term::prop(),
        Type => Term::t(),
        Variable(index) => {
            if index == replaced_index {
                replacement.to_owned()
            } else {
                Term::variable(index)
            }
        }
        Recursive(kind, children) => match kind {
            Lambda | ForAll => Term::recursive(
                kind,
                [
                    substitute_one(
                        children[0].get().as_term_ref(),
                        replaced_index + 1,
                        replacement,
                    )
                    .as_term_ref(),
                    substitute_one(children[1].get().as_term_ref(), replaced_index, replacement)
                        .as_term_ref(),
                ],
            ),
            Apply => Term::recursive(
                kind,
                [
                    substitute_one(children[0].get().as_term_ref(), replaced_index, replacement)
                        .as_term_ref(),
                    substitute_one(children[1].get().as_term_ref(), replaced_index, replacement)
                        .as_term_ref(),
                ],
            ),
        },
    }
}

pub fn naive_fully_reduce(term: TermRef) -> Term {
    use RecursiveTermKind::*;
    use TermKind::*;
    match term.kind() {
        Prop | Type | Variable(_) => term.to_owned(),
        Recursive(kind, children) => {
            if kind == Apply {
                if let Recursive(Lambda, [_, lambda_body]) = children[0].get().kind() {
                    return naive_fully_reduce(
                        substitute_one(
                            lambda_body.get().as_term_ref(),
                            0,
                            children[1].get().as_term_ref(),
                        )
                        .as_term_ref(),
                    );
                }
            }
            Term::recursive(
                kind,
                [
                    naive_fully_reduce(children[0].get().as_term_ref()).as_term_ref(),
                    naive_fully_reduce(children[1].get().as_term_ref()).as_term_ref(),
                ],
            )
        }
    }
}

pub fn naive_type_check(term: TermRef, context: &[TermRef]) -> Option<TypeCheckResult> {
    use RecursiveTermKind::*;
    use TermKind::*;
    use TypeCheckResult::*;
    Some(match term.kind() {
        Prop => HasType(Term::t()),
        Type => NoType,
        Variable(index) => HasType(context.get(index as usize)?.to_owned()),
        Recursive(kind, children) => match kind {
            Lambda | ForAll => {
                let argument_type = children[0].get();
                let HasType(argument_type_type) = naive_type_check(argument_type.as_term_ref(), context)? else { return Some(NoType); };
                if argument_type_type != Term::prop() && argument_type_type != Term::t() {
                    return Some(NoType);
                }

                let child_context: Vec<_> = iter::once(argument_type.as_term_ref())
                    .chain(context.iter().copied())
                    .collect();
                let HasType(body_type) = naive_type_check(children[1].get().as_term_ref(), &child_context)? else { return Some(NoType); };
                if kind == ForAll {
                    if body_type != Term::prop() && body_type != Term::t() {
                        return Some(NoType);
                    }
                    HasType(body_type)
                } else {
                    HasType(Term::recursive(
                        ForAll,
                        [children[0].get().as_term_ref(), body_type.as_term_ref()],
                    ))
                }
            }
            Apply => {
                let HasType(function_type) = naive_type_check(children[0].get().as_term_ref(), context)? else { return Some(NoType); };
                let Recursive(ForAll, [required_argument_type, return_type]) = function_type.kind() else { return Some(NoType); };
                let required_argument_type = required_argument_type.get();
                let HasType(passed_argument_type) = naive_type_check(children[1].get().as_term_ref(), context)? else { return Some(NoType); };
                if passed_argument_type != required_argument_type {
                    if is_fully_reduced(passed_argument_type.as_term_ref())
                        && is_fully_reduced(required_argument_type.as_term_ref())
                    {
                        return Some(NoType);
                    } else {
                        return None;
                    }
                }
                HasType(substitute_one(
                    return_type.get().as_term_ref(),
                    0,
                    passed_argument_type.as_term_ref(),
                ))
            }
        },
    })
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct JudgmentContext {
    assumed_argument_types_of_containing_lambdas_and_foralls: Vec<Term>,
}

impl JudgmentContext {
    pub fn with_extra_lambda_or_forall_with_argument_type(&self, new_argument_type: Term) -> Self {
        JudgmentContext {
            assumed_argument_types_of_containing_lambdas_and_foralls: iter::once(new_argument_type)
                .chain(
                    self.assumed_argument_types_of_containing_lambdas_and_foralls
                        .iter()
                        .cloned(),
                )
                .collect(),
        }
    }
}
/*
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct TypeJudgmentType {
    context: JudgmentContext,
    value: Term,
    type_of_value: Term,
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct IllTypednessJudgmentType {
    context: JudgmentContext,
    value: Term,
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct Judgment<T>(T);

pub struct TypeDecision {
    context: JudgmentContext,
    value: Term,
    type_of_value: Option<Term>,
}

impl IllTypednessJudgmentType {
    pub fn of_type() -> Judgment<IllTypednessJudgmentType> {
        Judgment(IllTypednessJudgmentType {
            context: JudgmentContext {
                assumed_argument_types_of_containing_lambdas_and_foralls: vec![],
            },
            value: Term::t(),
        })
    }
}

impl TypeJudgmentType {
    pub fn of_prop() -> Judgment<TypeJudgmentType> {
        Judgment(TypeJudgmentType {
            context: JudgmentContext {
                assumed_argument_types_of_containing_lambdas_and_foralls: vec![],
            },
            value: Term::prop(),
            type_of_value: Term::t(),
        })
    }
    pub fn judgments_this_would_be_satisfied_by(&self) -> Option<ArrayVec<TypeJudgmentType, 3>> {
        let trivial: Option<ArrayVec<TypeJudgmentType, 3>> = Some(ArrayVec::new());
        const IMPOSSIBLE: Option<ArrayVec<TypeJudgmentType, 3>> = None;
        match self.value.as_term_ref().kind() {
            TermKind::Prop => trivial,
            TermKind::Type => IMPOSSIBLE,
            TermKind::Variable(v) => {
                if self
                    .context
                    .assumed_argument_types_of_containing_lambdas_and_foralls[v as usize]
                    == self.type_of_value
                {
                    trivial
                } else {
                    IMPOSSIBLE
                }
            }
            TermKind::Recursive(kind, children) => {
                use RecursiveTermKind::*;
                let mut result = ArrayVec::new();
                match kind {
                    ForAll => {
                        let argtype = children[0].get();
                        result.push(TypeJudgmentType {
                            context: self.context.clone(),
                            value: argtype.clone(),
                            type_of_value: todo!(),
                        });
                        result.push(TypeJudgmentType {
                            context: self
                                .context
                                .with_extra_lambda_or_forall_with_argument_type(argtype),
                            value: children[1].get(),
                            type_of_value: self.type_of_value.clone(),
                        });
                    }
                    Lambda => {
                        let argtype = children[0].get();
                        result.push(TypeJudgmentType {
                            context: self.context.clone(),
                            value: argtype.clone(),
                            type_of_value: todo!(),
                        });
                        result.push(TypeJudgmentType {
                            context: self
                                .context
                                .with_extra_lambda_or_forall_with_argument_type(argtype),
                            value: children[1].get(),
                            type_of_value: self.type_of_value.clone(),
                        });
                    }
                    Apply => {}
                }
                Some(result)
            }
        }
    }
    pub fn of_forall(
        term: Term,
        judgment_of_argument_type: TypeJudgmentType,
        judgment_of_return_type: TypeJudgmentType,
    ) -> TypeJudgmentType {
        let TermKind::Recursive(RecursiveTermKind::ForAll, [argtype, body]) = term.kind() else { panic!() };
        let argtype = argtype.get();
        let body = body.get();
        assert!(judgment_of_argument_type.value == argtype);
        assert!(judgment_of_return_type.value == body);
        assert!(
            judgment_of_return_type
                .context
                .assumed_argument_types_of_containing_lambdas_and_foralls[0]
                == argtype
        );
        let new_args = judgment_of_return_type
            .context
            .assumed_argument_types_of_containing_lambdas_and_foralls[1..]
            .to_owned();
        TypeJudgmentType {
            context: JudgmentContext {
                assumed_argument_types_of_containing_lambdas_and_foralls: new_args,
            },
            value: term,
            type_of_value: judgment_of_return_type.type_of_value,
        }
    }
}

impl TypeDecision {}
*/
