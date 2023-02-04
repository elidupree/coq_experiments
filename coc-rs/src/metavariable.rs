use crate::constructors::{
    ArgsCompoundView, ArgsCompoundViewCases, ConstructorView, DataArgumentView, Notation,
    PreconditionView, TypeView, COC,
};
use arrayvec::ArrayVec;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::BTreeMap;
use std::iter::zip;
use uuid::Uuid;

#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Default, Debug,
)]
pub struct MetavariableId(pub Uuid);

#[derive(Serialize, Deserialize, Debug)]
pub struct Metavariable {
    pub name: String,
    pub typename: String,
    pub type_parameters: Vec<Option<MetavariableId>>,
    pub constructor: Option<MetavariableConstructor>,
    // #[serde(skip)]
    // pub back_references: Vec<MetavariableId>,
}

#[derive(Copy, Clone, Debug)]
pub struct MetavariableView<'a> {
    id: MetavariableId,
    type_definition: TypeView<'static>,
    instance: &'a Metavariable,
    environment: &'a Environment,
}

#[derive(Copy, Clone, Debug)]
pub struct MetavariableTypeParameterView<'a> {
    index: usize,
    instance: Option<MetavariableId>,
    datatype: TypeView<'static>,
    metavariable: MetavariableView<'a>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct MetavariableConstructor {
    pub name: String,
    pub data_arguments: BTreeMap<String, Option<MetavariableId>>,
    pub preconditions: Vec<Option<MetavariableId>>,
}

#[derive(Copy, Clone, Debug)]
pub struct MetavariableConstructorView<'a> {
    instance: &'a MetavariableConstructor,
    constructor_definition: ConstructorView<'static>,
    metavariable: MetavariableView<'a>,
}

#[derive(Copy, Clone, Debug)]
pub struct MetavariableDataArgumentView<'a> {
    instance: Option<MetavariableId>,
    definition: DataArgumentView<'static>,
    constructor: MetavariableConstructorView<'a>,
}

#[derive(Copy, Clone, Debug)]
pub struct MetavariablePreconditionView<'a> {
    instance: Option<MetavariableId>,
    definition: PreconditionView<'static>,
    constructor: MetavariableConstructorView<'a>,
}

#[derive(Copy, Clone, Debug)]
pub struct MetavariableResultingTypeParameterView<'a> {
    goal: Option<MetavariableId>,
    definition: ArgsCompoundView<'static>,
    constructor: MetavariableConstructorView<'a>,
}

#[derive(Default, Debug)]
pub struct Environment {
    metavariables: BTreeMap<MetavariableId, Metavariable>,
}

impl<'a> MetavariableView<'a> {
    pub fn id(&self) -> MetavariableId {
        self.id
    }
    pub fn name(&self) -> &'a str {
        &self.instance.name
    }
    pub fn typename(&self) -> &'static str {
        self.type_definition.name()
    }
    pub fn ty(&self) -> TypeView<'static> {
        self.type_definition
    }
    pub fn type_parameters(&self) -> impl Iterator<Item = MetavariableTypeParameterView<'a>> + '_ {
        zip(
            self.instance.type_parameters.iter().copied(),
            self.type_definition.type_parameters(),
        )
        .enumerate()
        .map(
            |(index, (definition, datatype))| MetavariableTypeParameterView {
                index,
                instance: definition,
                datatype,
                metavariable: *self,
            },
        )
    }
    pub fn type_parameter(&self, index: usize) -> MetavariableTypeParameterView<'a> {
        MetavariableTypeParameterView {
            index,
            instance: self.instance.type_parameters[index],
            datatype: self.type_definition.type_parameter(index),
            metavariable: *self,
        }
    }
    pub fn constructor(&self) -> Option<MetavariableConstructorView<'a>> {
        self.instance
            .constructor
            .as_ref()
            .map(|constructor| MetavariableConstructorView {
                instance: constructor,
                constructor_definition: self.type_definition.constructor(&constructor.name),
                metavariable: *self,
            })
    }
    pub fn existing_children(&self) -> impl Iterator<Item = MetavariableView<'a>> + '_ {
        let constructor = self.constructor();
        self.type_parameters()
            .map(|a| a.child())
            .chain(constructor.into_iter().flat_map(|constructor| {
                constructor
                    .data_arguments()
                    .map(|a| a.child())
                    .chain(constructor.preconditions().map(|a| a.child()))
            }))
            .flatten()
    }
}
impl<'a> MetavariableTypeParameterView<'a> {
    pub fn index(&self) -> usize {
        self.index
    }
    pub fn typename(&self) -> &'static str {
        self.datatype.name()
    }
    pub fn datatype(&self) -> TypeView<'static> {
        self.datatype
    }
    pub fn child(&self) -> Option<MetavariableView<'a>> {
        self.instance
            .map(|id| self.metavariable.environment.get(id).unwrap())
    }
}
impl<'a> MetavariableConstructorView<'a> {
    pub fn name(&self) -> &'static str {
        self.constructor_definition.name()
    }
    pub fn notation(&self) -> Option<&'static Notation<String>> {
        self.constructor_definition.notation()
    }
    pub fn data_arguments(&self) -> impl Iterator<Item = MetavariableDataArgumentView<'a>> + 'a {
        let constructor = *self;
        self.constructor_definition
            .data_arguments()
            .map(move |definition| MetavariableDataArgumentView {
                instance: *constructor
                    .instance
                    .data_arguments
                    .get(definition.name())
                    .unwrap(),
                definition,
                constructor,
            })
    }
    pub fn data_argument_indexed(&self, index: usize) -> MetavariableDataArgumentView<'a> {
        let definition = self.constructor_definition.data_argument_indexed(index);
        MetavariableDataArgumentView {
            instance: *self.instance.data_arguments.get(definition.name()).unwrap(),
            definition,
            constructor: *self,
        }
    }
    pub fn data_argument_named(&self, name: &str) -> MetavariableDataArgumentView<'a> {
        MetavariableDataArgumentView {
            instance: *self.instance.data_arguments.get(name).unwrap(),
            definition: self.constructor_definition.data_argument_named(name),
            constructor: *self,
        }
    }
    pub fn preconditions(&self) -> impl Iterator<Item = MetavariablePreconditionView<'a>> + 'a {
        let constructor = *self;
        zip(
            &self.instance.preconditions,
            self.constructor_definition.preconditions(),
        )
        .map(
            move |(&instance, definition)| MetavariablePreconditionView {
                instance,
                definition,
                constructor,
            },
        )
    }
    pub fn precondition(&self, index: usize) -> MetavariablePreconditionView<'a> {
        let definition = self.constructor_definition.precondition(index);
        MetavariablePreconditionView {
            instance: self.instance.preconditions[index],
            definition,
            constructor: *self,
        }
    }
    pub fn resulting_type_parameters(
        &self,
    ) -> impl Iterator<Item = MetavariableResultingTypeParameterView<'a>> + '_ {
        zip(
            self.constructor_definition.resulting_type_parameters(),
            &self.metavariable.instance.type_parameters,
        )
        .map(
            |(definition, &goal)| MetavariableResultingTypeParameterView {
                goal,
                definition,
                constructor: *self,
            },
        )
    }
}

impl<'a> MetavariableDataArgumentView<'a> {
    pub fn index(&self) -> usize {
        self.definition.index()
    }
    pub fn name(&self) -> &'static str {
        self.definition.name()
    }
    pub fn typename(&self) -> &'static str {
        self.definition.typename()
    }
    pub fn datatype(&self) -> TypeView<'static> {
        self.definition.datatype()
    }
    pub fn child(&self) -> Option<MetavariableView<'a>> {
        self.instance
            .map(|id| self.constructor.metavariable.environment.get(id).unwrap())
    }
}

impl<'a> MetavariablePreconditionView<'a> {
    pub fn index(&self) -> usize {
        self.definition.index()
    }
    pub fn predicate_type(&self) -> TypeView<'static> {
        self.definition.predicate_type()
    }
    pub fn child(&self) -> Option<MetavariableView<'a>> {
        self.instance
            .map(|id| self.constructor.metavariable.environment.get(id).unwrap())
    }
    pub fn type_parameters(&self) -> impl Iterator<Item = ArgsCompoundView<'static>> + '_ {
        self.definition.type_parameters()
    }
    pub fn type_parameter(&self, index: usize) -> ArgsCompoundView<'static> {
        self.definition.type_parameter(index)
    }
}
impl<'a> MetavariableResultingTypeParameterView<'a> {
    pub fn datatype(&self) -> TypeView<'static> {
        self.definition.datatype()
    }
    pub fn goal(&self) -> Option<MetavariableView<'a>> {
        self.goal
            .map(|id| self.constructor.metavariable.environment.get(id).unwrap())
    }
    pub fn inferred(&self) -> ArgsCompoundView<'static> {
        self.definition
    }
}

#[derive(Debug)]
pub struct LocalValidity {
    pub type_parameters_valid: Vec<bool>,
    pub constructor_valid: bool,
    pub data_arguments_valid: BTreeMap<String, bool>,
    pub preconditions_valid: Vec<bool>,
    pub return_type_parameters_valid: Vec<bool>,
}

impl LocalValidity {
    pub fn is_valid(&self) -> bool {
        self.constructor_valid
            && self
                .type_parameters_valid
                .iter()
                .chain(self.data_arguments_valid.values())
                .chain(self.preconditions_valid.iter())
                .all(|b| *b)
    }
}

impl Environment {
    pub fn get(&self, id: MetavariableId) -> Option<MetavariableView> {
        let definition = self.metavariables.get(&id)?;
        Some(MetavariableView {
            id,
            type_definition: COC.get(&definition.typename),
            instance: definition,
            environment: self,
        })
    }
    pub fn get_mut(&mut self, id: MetavariableId) -> &mut Metavariable {
        self.metavariables.get_mut(&id).unwrap()
    }

    #[allow(clippy::only_used_in_recursion)]
    pub fn metavariable_matches_datavalue(
        &self,
        metavariable: Option<MetavariableView>,
        value: &ArgsCompoundView,
        data_arguments: &BTreeMap<String, Option<MetavariableId>>,
    ) -> bool {
        let Some(metavariable) = metavariable else { return false; };
        if metavariable.typename() != value.datatype().name() {
            return false;
        }
        match value.cases() {
            ArgsCompoundViewCases::Argument(argument) => {
                data_arguments.get(argument.name()).unwrap() == &Some(metavariable.id())
            }
            ArgsCompoundViewCases::Constructor {
                constructor: required_constructor,
                arguments: required_constructor_arguments,
            } => {
                let Some(constructor) = metavariable.constructor() else { return false; };
                constructor.name() == required_constructor.name()
                    && zip(required_constructor_arguments, constructor.data_arguments()).all(
                        |(r, a)| self.metavariable_matches_datavalue(a.child(), &r, data_arguments),
                    )
            }
        }
    }
    pub fn local_validity(&self, metavariable: MetavariableView) -> LocalValidity {
        let type_parameters_valid = metavariable
            .type_parameters()
            .map(|parameter| match parameter.child() {
                None => false,
                Some(other) => other.typename() == parameter.datatype().name(),
            })
            .collect();
        let constructor_valid;
        let data_arguments_valid;
        let preconditions_valid;
        let return_type_parameters_valid;
        if let Some(constructor) = metavariable.constructor() {
            constructor_valid = true;
            data_arguments_valid = constructor
                .data_arguments()
                .map(|argument| {
                    (
                        argument.name().to_owned(),
                        match argument.child() {
                            None => false,
                            Some(other) => other.typename() == argument.datatype().name(),
                        },
                    )
                })
                .collect();

            preconditions_valid = constructor
                .preconditions()
                .map(|precondition| match precondition.child() {
                    None => false,
                    Some(other) => {
                        if other.typename() != precondition.predicate_type().name() {
                            return false;
                        }
                        zip(other.type_parameters(), precondition.type_parameters()).all(
                            |(provided, needed)| {
                                self.metavariable_matches_datavalue(
                                    provided.child(),
                                    &needed,
                                    &constructor.instance.data_arguments,
                                )
                            },
                        )
                    }
                })
                .collect();

            return_type_parameters_valid = constructor
                .resulting_type_parameters()
                .map(|parameter| {
                    self.metavariable_matches_datavalue(
                        parameter.goal(),
                        &parameter.inferred(),
                        &constructor.instance.data_arguments,
                    )
                })
                .collect();
        } else {
            constructor_valid = false;
            data_arguments_valid = Default::default();
            preconditions_valid = Default::default();
            return_type_parameters_valid = Default::default();
        }
        LocalValidity {
            type_parameters_valid,
            constructor_valid,
            data_arguments_valid,
            preconditions_valid,
            return_type_parameters_valid,
        }
    }

    // fn populate_back_references(&mut self, id: MetavariableId) {
    //     let metavariable = self.get(id);
    //     for reference in metavariable
    //         .type_parameters
    //         .iter()
    //         .chain(metavariable.constructor.iter().flat_map(|constructor| {
    //             constructor
    //                 .arguments
    //                 .values()
    //                 .chain(&constructor.preconditions)
    //         }))
    //         .flatten()
    //         .copied()
    //         .collect::<Vec<_>>()
    //     {
    //         self.get_mut(reference).back_references.push(id);
    //     }
    // }

    pub fn create_metavariable(&mut self, typename: String) -> MetavariableId {
        let id = MetavariableId(Uuid::new_v4());
        let type_definition = COC.get(&typename);
        self.metavariables.insert(
            id,
            Metavariable {
                name: "".to_string(),
                typename,
                type_parameters: type_definition.type_parameters().map(|_| None).collect(),
                constructor: None,
            },
        );
        id
    }

    pub fn set_type_parameter(
        &mut self,
        id: MetavariableId,
        index: usize,
        value: Option<MetavariableId>,
    ) {
        self.get_mut(id).type_parameters[index] = value;
    }

    pub fn set_constructor(&mut self, id: MetavariableId, value: Option<String>) {
        let metavariable = self.get_mut(id);
        let type_definition = COC.get(&metavariable.typename);
        metavariable.constructor = value.map(|name| {
            let constructor = type_definition.constructor(&name);
            MetavariableConstructor {
                name,
                data_arguments: constructor
                    .data_arguments()
                    .map(|a| (a.name().to_owned(), None))
                    .collect(),
                preconditions: constructor.preconditions().map(|_| None).collect(),
            }
        });
    }

    pub fn set_data_argument_named(
        &mut self,
        id: MetavariableId,
        name: &str,
        value: Option<MetavariableId>,
    ) {
        let constructor = self.get_mut(id).constructor.as_mut().unwrap();
        *constructor.data_arguments.get_mut(name).unwrap() = value;
    }

    pub fn set_data_argument_indexed(
        &mut self,
        id: MetavariableId,
        index: usize,
        value: Option<MetavariableId>,
    ) {
        let name = self
            .get(id)
            .unwrap()
            .constructor()
            .unwrap()
            .data_argument_indexed(index)
            .name();
        self.set_data_argument_named(id, name, value);
    }

    pub fn set_precondition(
        &mut self,
        id: MetavariableId,
        index: usize,
        value: Option<MetavariableId>,
    ) {
        let constructor = self.get_mut(id).constructor.as_mut().unwrap();
        *constructor.preconditions.get_mut(index).unwrap() = value;
    }

    pub fn rename(&mut self, id: MetavariableId, new_name: impl Into<String>) {
        self.get_mut(id).name = new_name.into();
    }

    pub fn metavariables(&self) -> impl Iterator<Item = MetavariableView> + '_ {
        self.metavariables
            .iter()
            .map(|(&id, instance)| MetavariableView {
                id,
                type_definition: COC.get(&instance.typename),
                instance,
                environment: self,
            })
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum CanMatch {
    Yes,
    Maybe,
    No,
}

impl Environment {
    #[allow(clippy::only_used_in_recursion)]
    fn fill_in_args_to_make_datavalue_match_metavariable(
        &self,
        metavariable: Option<MetavariableView>,
        value: &ArgsCompoundView,
        data_arguments: &mut BTreeMap<String, Option<MetavariableId>>,
    ) -> CanMatch {
        let Some(metavariable) = metavariable else { return CanMatch::Maybe; };
        if metavariable.typename() != value.datatype().name() {
            return CanMatch::No;
        }
        match value.cases() {
            ArgsCompoundViewCases::Argument(argument) => {
                let arg = data_arguments.get_mut(argument.name()).unwrap();
                if arg.is_none() {
                    *arg = Some(metavariable.id())
                }
                if *arg == Some(metavariable.id()) {
                    CanMatch::Yes
                } else {
                    // if {
                    //     self.replace(*arg, id);
                    // }
                    CanMatch::No
                }
            }
            ArgsCompoundViewCases::Constructor {
                constructor: required_constructor,
                arguments: required_constructor_arguments,
            } => {
                let Some(constructor) = metavariable.constructor() else { return CanMatch::Maybe; };
                if constructor.name() != required_constructor.name() {
                    return CanMatch::No;
                }
                let mut submatch_results = CanMatch::Yes;
                for (r, a) in zip(
                    required_constructor_arguments,
                    required_constructor.data_arguments(),
                ) {
                    let submatch_possible = self.fill_in_args_to_make_datavalue_match_metavariable(
                        constructor.data_argument_named(a.name()).child(),
                        &r,
                        data_arguments,
                    );
                    match submatch_possible {
                        CanMatch::Yes => {}
                        CanMatch::Maybe => submatch_results = CanMatch::Maybe,
                        CanMatch::No => return CanMatch::No,
                    }
                }
                submatch_results
            }
        }
    }

    fn make_metavariable_that_matches_data_value(
        &mut self,
        value: &ArgsCompoundView,
        data_arguments: &mut BTreeMap<String, Option<MetavariableId>>,
    ) -> MetavariableId {
        if let Some(existing) = self.metavariables().find(|&metavariable| {
            self.metavariable_matches_datavalue(Some(metavariable), value, data_arguments)
        }) {
            return existing.id();
        }
        let new_id = self.create_metavariable(value.datatype().name().to_owned());
        match value.cases() {
            ArgsCompoundViewCases::Argument(argument) => {
                let existing = data_arguments.get_mut(argument.name()).unwrap();
                assert!(
                    existing.is_none(),
                    "if it was Some then the variable it points to should have matched"
                );
                *existing = Some(new_id);
            }
            ArgsCompoundViewCases::Constructor {
                constructor,
                arguments,
            } => {
                self.set_constructor(new_id, Some(constructor.name().to_owned()));
                for (argument, argument_definition) in zip(arguments, constructor.data_arguments())
                {
                    let new_child_id =
                        self.make_metavariable_that_matches_data_value(&argument, data_arguments);
                    self.set_data_argument_named(
                        new_id,
                        argument_definition.name(),
                        Some(new_child_id),
                    );
                }
            }
        }
        new_id
    }

    pub fn constructor_possible(
        &self,
        metavariable: MetavariableView,
        constructor_name: &str,
    ) -> CanMatch {
        let constructor_definition = metavariable.ty().constructor(constructor_name);
        let mut data_arguments: BTreeMap<String, Option<MetavariableId>> = constructor_definition
            .data_arguments()
            .map(|a| (a.name().to_owned(), None))
            .collect();
        let mut match_results = CanMatch::Yes;
        for (required, produced) in zip(
            metavariable.type_parameters(),
            constructor_definition.resulting_type_parameters(),
        ) {
            let match_possible = self.fill_in_args_to_make_datavalue_match_metavariable(
                required.child(),
                &produced,
                &mut data_arguments,
            );
            match match_possible {
                CanMatch::Yes => {}
                CanMatch::Maybe => match_results = CanMatch::Maybe,
                CanMatch::No => return CanMatch::No,
            }
        }

        match_results
    }

    pub fn autofill(&mut self, id: MetavariableId) {
        let metavariable = self.get(id).unwrap();

        if metavariable.constructor().is_none() {
            let mut possible_constructors: ArrayVec<&str, 2> = ArrayVec::new();
            for constructor in metavariable.ty().constructors() {
                match self.constructor_possible(metavariable, constructor.name()) {
                    CanMatch::Yes => {
                        possible_constructors.clear();
                        possible_constructors.push(constructor.name());
                        break;
                    }
                    CanMatch::Maybe => {
                        let _ = possible_constructors.try_push(constructor.name());
                    }
                    CanMatch::No => {}
                }
            }
            if let &[only_constructor_name] = &*possible_constructors {
                self.set_constructor(id, Some(only_constructor_name.to_owned()));
            }
        }
        let metavariable = self.get(id).unwrap();

        if let Some(constructor) = metavariable.constructor() {
            let mut data_arguments = constructor.instance.data_arguments.clone();
            for parameter in constructor.resulting_type_parameters() {
                self.fill_in_args_to_make_datavalue_match_metavariable(
                    parameter.goal(),
                    &parameter.inferred(),
                    &mut data_arguments,
                );
            }
            for precondition in constructor.preconditions() {
                if let Some(child) = precondition.child() {
                    for (required, defined) in
                        zip(precondition.type_parameters(), child.type_parameters())
                    {
                        self.fill_in_args_to_make_datavalue_match_metavariable(
                            defined.child(),
                            &required,
                            &mut data_arguments,
                        );
                    }
                }
            }
            if data_arguments != constructor.instance.data_arguments {
                self.get_mut(id)
                    .constructor
                    .as_mut()
                    .unwrap()
                    .data_arguments = data_arguments;
                return self.autofill(id);
            }
            // should be a for loop, but Rust won't let us drop the borrow before returning
            let mut preconditions = constructor.preconditions();
            while let Some(precondition) = preconditions.next() {
                if precondition.child().is_none() {
                    // if there's already a metavariable that satisfies this, use it:
                    // should be a for loop, but Rust won't let us drop the borrow before returning
                    let mut others = self.metavariables();
                    while let Some(other) = others.next() {
                        let mut set_data_arg = None;
                        let typename = precondition.predicate_type().name();
                        if other.typename() == typename
                            && zip(
                                    precondition.type_parameters(),
                                    other.type_parameters(),
                            )
                            .enumerate()
                            .all(
                                |(index, (required, provided))| {
                                    // certain parameters are "fully determined" by the other parameters,
                                    // so we count something as "matching" if we do not specify that parameter
                                    // TODO fix duplicate code id f9gd67fg8re8g
                                    if (typename == "FormulaSubstitution"
                                            || typename == "BindingSubstitution")
                                        && index == 3
                                    {
                                        let ArgsCompoundViewCases::Argument(argument) = required.cases() else {unreachable!()};
                                        if data_arguments[argument.name()].is_none() {
                                            set_data_arg = Some((argument.name(), provided.instance, typename));
                                            return true
                                        }
                                    }
                                    self.metavariable_matches_datavalue(
                                        provided.child(),
                                        &required,
                                        &constructor.instance.data_arguments,
                                    )
                                },
                            )
                        {
                            let precondition_index = precondition.index();
                            let other_id = other.id();
                            drop((metavariable, preconditions, others));
                            self.get_mut(id).constructor.as_mut().unwrap().preconditions
                                [precondition_index] = Some(other_id);
                            if let Some((argname, existing, typename)) = set_data_arg{
                                let new_id = existing.unwrap_or_else(|| {
                                    let new_id = self.create_metavariable(typename.to_owned());
                                    // TODO fix duplicate code id f9gd67fg8re8g
                                    self.get_mut(other_id).type_parameters[3] = Some(new_id);
                                    new_id
                                });
                                *self.get_mut(id).constructor.as_mut().unwrap().data_arguments.get_mut (argname).unwrap() = Some (new_id);
                            }
                            return self.autofill(id);
                        }
                    }

                    let precondition_index = precondition.index();
                    let precondition_typename = precondition.predicate_type().name().to_owned();
                    let precondition_type_parameters: Vec<(usize, ArgsCompoundView<'static>)> =
                        precondition.type_parameters().enumerate().collect();
                    drop((metavariable, preconditions, others));
                    // If there's not one already ... create it!
                    let new_precondition_id = self.create_metavariable(precondition_typename);
                    self.get_mut(id).constructor.as_mut().unwrap().preconditions
                        [precondition_index] = Some(new_precondition_id);
                    for (index, required) in precondition_type_parameters {
                        let new_parameter_id = self.make_metavariable_that_matches_data_value(
                            &required,
                            &mut data_arguments,
                        );
                        self.get_mut(new_precondition_id).type_parameters[index] =
                            Some(new_parameter_id);
                    }
                    self.get_mut(id)
                        .constructor
                        .as_mut()
                        .unwrap()
                        .data_arguments = data_arguments;
                    return self.autofill(id);
                }
            }
        }

        // for type_parameter in &metavariable.type_parameters {
        //     if type_parameter.is_none() {
        //         for (&other_id, _other) in &self.metavariables {
        //             if self.metavariable_matches_datavalue(
        //                 Some(other_id),
        //                 resulting,
        //                 typename,
        //                 &constructor.data_arguments,
        //             ) {
        //                 self.get_mut(id).type_parameters[index]
        //             }
        //         }
        //     }
        // }
    }

    pub fn replace(&mut self, replaced: MetavariableId, replacement: MetavariableId) {
        for (&_id, metavariable) in &mut self.metavariables {
            for id in metavariable
                .type_parameters
                .iter_mut()
                .chain(metavariable.constructor.iter_mut().flat_map(|constructor| {
                    constructor
                        .data_arguments
                        .values_mut()
                        .chain(&mut constructor.preconditions)
                }))
                .flatten()
            {
                if *id == replaced {
                    *id = replacement;
                }
            }
        }
        self.metavariables.remove(&replaced);
    }
}

impl Serialize for Environment {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.metavariables.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Environment {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let metavariables = BTreeMap::<MetavariableId, Metavariable>::deserialize(deserializer)?;
        Ok(Environment { metavariables })
        // let mut result = Environment { metavariables };
        // for id in result.metavariables.keys().copied().collect::<Vec<_>>() {
        //     result.populate_back_references(id);
        // }
        // Ok(result)
    }
}
