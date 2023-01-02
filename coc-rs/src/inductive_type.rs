use extend::ext;
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
        for (name, ty) in arguments.into_iter().collect::<Vec<_>>().into_iter().rev() {
            result = Self::forall(name, ty, result)
        }
        result
    }
    fn lambda_chain(
        arguments: impl IntoIterator<Item = (Option<String>, Self)>,
        return_value: Self,
    ) -> Self {
        let mut result = return_value;
        for (name, ty) in arguments.into_iter().collect::<Vec<_>>().into_iter().rev() {
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
        Self::variable_impl(name.into())
    }
}

//pub fn lambda (name: impl ToString, body: )

pub struct TypeConstructorDefinition<T> {
    name: String,
    nonrecursive_arguments: Vec<(String, T)>,
    recursive_arguments: Vec<String>,
}

pub struct InductivePredicateConstructorDefinition<T> {
    name: String,
    arguments: Vec<(String, T)>,
    return_type: T,
}

pub struct TypeDefinition<T> {
    constructors: Vec<TypeConstructorDefinition<T>>,
}

pub struct InductivePredicateDefinition<T> {
    constructors: Vec<InductivePredicateConstructorDefinition<T>>,
    indices: Vec<(String, T)>,
}

pub struct TypeDefinitionGeneratedTerms<T> {
    raw_type: T,
    raw_constructors: Vec<(String, T)>,
    induction_predicate: T,
    induction_predicate_constructors: Vec<(String, T)>,
    // inductive_type: T,
    // inductive_constructors: Vec<(String, T)>,
}

pub struct InductivePredicateDefinitionGeneratedTerms<T> {
    induction_predicate: T,
    induction_predicate_constructors: Vec<(String, T)>,
}

impl<T: ConstructUsingNames + Clone> TypeConstructorDefinition<T> {
    pub fn reducer_type(&self) -> T {
        T::forall_chain(
            self.nonrecursive_arguments
                .iter()
                .map(|(_name, ty)| (None, ty.clone()))
                .chain(
                    self.recursive_arguments
                        .iter()
                        .map(|_| (None, T::variable("P"))),
                ),
            T::variable("P"),
        )
    }
    pub fn constructor(&self, raw_type: &T, reducers: impl IntoIterator<Item = (String, T)>) -> T {
        let args: Vec<_> = self
            .nonrecursive_arguments
            .iter()
            .cloned()
            .chain(
                self.recursive_arguments
                    .iter()
                    .map(|name| (name.clone(), raw_type.clone())),
            )
            .collect();
        T::lambda_chain(
            args.iter()
                .map(|(name, ty)| (Some(name.clone()), ty.clone()))
                .chain(reducers.into_iter().map(|(name, ty)| (Some(name), ty))),
            T::apply_chain(
                T::variable(&self.name),
                args.iter().map(|(name, _ty)| T::variable(name)),
            ),
        )
    }
    pub fn inductive_predicate_constructor(
        &self,
        raw_type: &T,
        raw_constructor: &T,
    ) -> InductivePredicateConstructorDefinition<T> {
        let arguments: Vec<_> = self
            .nonrecursive_arguments
            .iter()
            .map(|(name, ty)| (name.clone(), ty.clone()))
            .chain(self.recursive_arguments.iter().flat_map(|name| {
                [
                    (name.clone(), raw_type.clone()),
                    (
                        format!("P{}", name),
                        T::apply(T::variable("P"), T::variable(name)),
                    ),
                ]
            }))
            .collect();
        let return_arguments = self
            .nonrecursive_arguments
            .iter()
            .map(|(name, _ty)| T::variable(name))
            .chain(
                self.recursive_arguments
                    .iter()
                    .map(|name| T::variable(name)),
            );
        InductivePredicateConstructorDefinition {
            name: format!("{}IsInductive", self.name),
            arguments,
            return_type: T::apply(
                T::variable("P"),
                T::apply_chain(raw_constructor.clone(), return_arguments),
            ),
        }
    }
}

impl<T: ConstructUsingNames + Clone> InductivePredicateConstructorDefinition<T> {
    pub fn inductive_reducer_type(&self) -> T {
        T::forall_chain(
            self.arguments
                .iter()
                .map(|(name, ty)| (Some(name.clone()), ty.clone())),
            self.return_type.clone(),
        )
    }
    pub fn constructor(&self, reducers: impl IntoIterator<Item = (String, T)>) -> T {
        T::lambda_chain(
            self.arguments
                .iter()
                .map(|(name, ty)| (Some(name.clone()), ty.clone()))
                .chain(reducers.into_iter().map(|(name, ty)| (Some(name), ty))),
            T::apply_chain(
                T::variable(&self.name),
                self.arguments.iter().map(|(name, _ty)| T::variable(name)),
            ),
        )
    }
}

impl<T: ConstructUsingNames + Clone> TypeDefinition<T> {
    pub fn generate_terms(&self) -> TypeDefinitionGeneratedTerms<T> {
        let raw_reducer_types: Vec<_> = self
            .constructors
            .iter()
            .map(TypeConstructorDefinition::reducer_type)
            .collect();
        let raw_type = T::forall_chain(
            iter::once((Some("P".into()), T::ty())).chain(
                iter::zip(&self.constructors, &raw_reducer_types)
                    .map(|(c, ty)| (Some(c.name.clone()), ty.clone())),
            ),
            T::variable("P"),
        );

        let raw_constructors: Vec<_> = self
            .constructors
            .iter()
            .map(|c| {
                c.constructor(
                    &raw_type,
                    iter::zip(&self.constructors, &raw_reducer_types)
                        .map(|(c, ty)| (c.name.clone(), ty.clone())),
                )
            })
            .collect();

        let induction_predicate_constructor_definitions: Vec<_> =
            iter::zip(&self.constructors, &raw_constructors)
                .map(|(c, raw_constructor)| {
                    c.inductive_predicate_constructor(&raw_type, raw_constructor)
                })
                .collect();

        let induction_predicate_definition = InductivePredicateDefinition {
            constructors: induction_predicate_constructor_definitions,
            indices: vec![("v".into(), raw_type.clone())],
        };

        let InductivePredicateDefinitionGeneratedTerms {
            induction_predicate,
            induction_predicate_constructors,
        } = induction_predicate_definition.generate_terms();

        TypeDefinitionGeneratedTerms {
            raw_type,
            raw_constructors: iter::zip(
                self.constructors.iter().map(|c| c.name.clone()),
                raw_constructors,
            )
            .collect(),
            induction_predicate,
            induction_predicate_constructors,
        }
    }

    pub fn term() -> Self {
        TypeDefinition {
            constructors: vec![
                TypeConstructorDefinition {
                    name: "Prop".into(),
                    nonrecursive_arguments: vec![],
                    recursive_arguments: vec![],
                },
                TypeConstructorDefinition {
                    name: "Type".into(),
                    nonrecursive_arguments: vec![],
                    recursive_arguments: vec![],
                },
                TypeConstructorDefinition {
                    name: "Variable".into(),
                    nonrecursive_arguments: vec![],
                    recursive_arguments: vec![],
                },
                TypeConstructorDefinition {
                    name: "ForAll".into(),
                    nonrecursive_arguments: vec![],
                    recursive_arguments: vec!["ArgumentType".into(), "ReturnType".into()],
                },
                TypeConstructorDefinition {
                    name: "Lambda".into(),
                    nonrecursive_arguments: vec![],
                    recursive_arguments: vec!["ArgumentType".into(), "ReturnValue".into()],
                },
                TypeConstructorDefinition {
                    name: "Apply".into(),
                    nonrecursive_arguments: vec![],
                    recursive_arguments: vec!["Function".into(), "Argument".into()],
                },
            ],
        }
    }
}

impl<T: ConstructUsingNames + Clone> InductivePredicateDefinition<T> {
    pub fn generate_terms(&self) -> InductivePredicateDefinitionGeneratedTerms<T> {
        let induction_predicate_reducer_types: Vec<_> = self
            .constructors
            .iter()
            .map(InductivePredicateConstructorDefinition::inductive_reducer_type)
            .collect();

        let induction_predicate = T::lambda_chain(
            self.indices
                .iter()
                .map(|(name, ty)| (Some(name.clone()), ty.clone())),
            T::forall_chain(
                iter::once((
                    Some("P".into()),
                    T::forall_chain(
                        self.indices
                            .iter()
                            .map(|(name, ty)| (Some(name.clone()), ty.clone())),
                        T::ty(),
                    ),
                ))
                .chain(iter::zip(
                    self.constructors.iter().map(|c| Some(c.name.clone())),
                    induction_predicate_reducer_types.iter().cloned(),
                )),
                T::apply_chain(
                    T::variable("P"),
                    self.indices.iter().map(|(name, _ty)| T::variable(name)),
                ),
            ),
        );

        let induction_predicate_constructors = self
            .constructors
            .iter()
            .map(|c| {
                (
                    c.name.clone(),
                    c.constructor(iter::zip(
                        self.constructors.iter().map(|c| c.name.clone()),
                        induction_predicate_reducer_types.iter().cloned(),
                    )),
                )
            })
            .collect();

        InductivePredicateDefinitionGeneratedTerms {
            induction_predicate,
            induction_predicate_constructors,
        }
    }
}
