use crate::term::RecursiveTermKind::*;
use crate::term::{RecursiveTermKind, Term, TermRef};
use extend::ext;
use std::collections::HashMap;
use std::iter;

pub trait ConstructUsingNames {
    fn forall(argument_name: Option<String>, argument_type: Self, return_type: Self) -> Self;
    fn lambda(argument_name: Option<String>, argument_type: Self, return_value: Self) -> Self;
    fn apply(f: Self, argument: Self) -> Self;
    fn variable_impl(name: String) -> Self;
    fn prop() -> Self;
    fn ty() -> Self;
}

#[ext]
impl<T: ConstructUsingNames> T {
    fn forall_chain(
        arguments: impl IntoIterator<Item = (Option<String>, Self)>,
        return_type: Self,
    ) -> Self {
        let mut result = return_type;
        for (name, ty) in arguments.collect::<Vec<_>>().into_iter().rev() {
            result = Self::forall(name, ty, result)
        }
        result
    }
    fn lambda_chain(
        arguments: impl IntoIterator<Item = (Option<String>, Self)>,
        return_value: Self,
    ) -> Self {
        let mut result = return_value;
        for (name, ty) in arguments.collect::<Vec<_>>().into_iter().rev() {
            result = Self::lambda(name, ty, result)
        }
        result
    }
    fn apply_chain(f: Self, arguments: impl IntoIterator<Item = Self>) -> Self {
        let mut result = f;
        for argument in arguments {
            result = Self::apply(result, argument)
        }
        result
    }
    fn variable(name: impl Into<String>) -> Self {
        Self::variable_impl(name)
    }
}

pub trait TermBuilder {
    fn build(&self, context: &HashMap<String, Term>) -> Term;
}

pub struct Apply {
    f: Box<dyn TermBuilder>,
    args: Vec<Box<dyn TermBuilder>>,
}

pub struct Lambda {
    args: Vec<(String, Box<dyn TermBuilder>)>,
    body: Box<dyn TermBuilder>,
}

macro_rules! apply {
    ($f:tt $args:tt+) => {
        Apply{
            f: Box::new($f),
            args: vec![$(Box::new ($args))*]
        }
    }
}

macro_rules! lambda {
    ($f:tt $body:tt+) => {
        Lambda {
            args: vec![$(Box::new ($args))*]
        }
    }
}

//pub fn lambda (name: impl ToString, body: )

pub struct InductiveConstructor<T> {
    name: String,
    nonrecursive_arguments: Vec<(String, T)>,
    // the data distinguishing each recursive argument is what the values of the indices are.
    // this isn't fully general, but it's all I need for the construction of the Term and TypeJudgment types.
    recursive_argument_indices: Vec<(String, Vec<T>)>,
    return_indices: Vec<T>,
}

pub struct InductiveTypeDefinition<T> {
    indices: Vec<(String, T)>,
    constructors: Vec<InductiveConstructor<T>>,
}

pub struct InductiveTypeDefinitionGeneratedTerms<T> {
    raw_type: T,
    raw_constructors: Vec<(String, T)>,
    induction_predicate: T,
    induction_constructors: Vec<(String, T)>,
    inductive_type: T,
    inductive_constructors: Vec<(String, T)>,
}

impl<T: ConstructUsingNames + Clone> InductiveConstructor<T> {
    pub fn raw_reducer_type(&self) -> T {
        T::forall_chain(
            self.nonrecursive_arguments
                .iter()
                .map(|(name, ty)| (None, ty.clone()))
                .chain(
                    self.recursive_argument_indices
                        .iter()
                        .map(|_| T::variable("P")),
                ),
            T::variable("P"),
        )
    }
    pub fn inductive_reducer_type(&self, raw_type: &T) -> T {
        T::forall_chain(
            self.nonrecursive_arguments
                .iter()
                .map(|(name, ty)| (Some(name.clone()), ty.clone()))
                .chain(
                    self.recursive_argument_indices
                        .iter()
                        .flat_map(|index_values| {
                            [
                                T::apply_chain(raw_type.clone(), index_values.iter().cloned()),
                                T::apply_chain(T::variable("P"), index_values.iter().cloned()),
                            ]
                        }),
                ),
            T::variable("P"),
        )
    }
    pub fn raw_constructor_args(&self, raw_type: &T) -> impl Iterator<Item = (String, T)> {
        constructor.nonrecursive_arguments.cloned().chain(
            constructor
                .recursive_argument_indices
                .map(|(name, _ty)| (Some(name.clone()), raw_type.clone())),
        )
    }
}

impl<T: ConstructUsingNames + Clone> InductiveTypeDefinition<T> {
    pub fn generate_terms(&self) -> InductiveTypeDefinitionGeneratedTerms<T> {
        let raw_reducer_types: Vec<_> = self
            .constructors
            .iter()
            .map(InductiveConstructor::raw_reducer_type)
            .collect();
        let raw_type = T::forall_chain(
            iter::once((Some("P".into()), T::ty())).chain(raw_reducer_types.clone()),
            T::variable("P"),
        );

        let raw_constructors: Vec<_> = self
            .constructors
            .iter()
            .map(|constructor: &InductiveConstructor<T>| {
                let args = constructor.raw_constructor_args(raw_type);
                let value = T::lambda_chain(
                    args.iter()
                        .map(|(name, ty)| (Some(name.clone()), ty.clone()))
                        .chain(
                            iter::zip(&self.constructors, &raw_reducer_types)
                                .map(|(c2, r2)| (Some(c2.name.clone()), r2)),
                        ),
                    T::apply_chain(
                        T::variable(&constructor.name),
                        args.into_iter().map(|name, _ty| T::variable(name)),
                    ),
                );
                (format!("raw{}", constructor.name), value)
            })
            .collect();

        let induction_predicate = T::forall_chain(
            iter::once((Some("P".into()), T::ty())).chain(raw_reducer_types.clone()),
            T::variable("P"),
        );
    }

    pub fn term() -> Self {
        InductiveTypeDefinition {
            indices: vec![],
            constructors: vec![
                InductiveConstructor {
                    name: "Prop".into(),
                    nonrecursive_arguments: vec![],
                    recursive_argument_indices: vec![],
                    return_indices: vec![],
                },
                InductiveConstructor {
                    name: "Type".into(),
                    nonrecursive_arguments: vec![],
                    recursive_argument_indices: vec![],
                    return_indices: vec![],
                },
                InductiveConstructor {
                    name: "Variable".into(),
                    nonrecursive_arguments: vec![],
                    recursive_argument_indices: vec![],
                    return_indices: vec![],
                },
                InductiveConstructor {
                    name: "ForAll".into(),
                    nonrecursive_arguments: vec![],
                    recursive_argument_indices: vec![
                        ("ArgumentType".into(), vec![]),
                        ("ReturnType".into(), vec![]),
                    ],
                    return_indices: vec![],
                },
                InductiveConstructor {
                    name: "Lambda".into(),
                    nonrecursive_arguments: vec![],
                    recursive_argument_indices: vec![
                        ("ArgumentType".into(), vec![]),
                        ("ReturnValue".into(), vec![]),
                    ],
                    return_indices: vec![],
                },
                InductiveConstructor {
                    name: "Apply".into(),
                    nonrecursive_arguments: vec![],
                    recursive_argument_indices: vec![
                        ("Function".into(), vec![]),
                        ("Argument".into(), vec![]),
                    ],
                    return_indices: vec![],
                },
            ],
        }
    }
}
