use crate::constructors::{ArgsCompoundView, ArgsCompoundViewCases, COC};
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

#[derive(Serialize, Deserialize, Debug)]
pub struct MetavariableConstructor {
    pub name: String,
    pub data_arguments: BTreeMap<String, Option<MetavariableId>>,
    pub preconditions: Vec<Option<MetavariableId>>,
}

#[derive(Default, Debug)]
pub struct Environment {
    metavariables: BTreeMap<MetavariableId, Metavariable>,
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
    pub fn get(&self, id: MetavariableId) -> &Metavariable {
        self.metavariables.get(&id).unwrap()
    }
    pub fn get_mut(&mut self, id: MetavariableId) -> &mut Metavariable {
        self.metavariables.get_mut(&id).unwrap()
    }

    pub fn metavariable_matches_datavalue(
        &self,
        id: Option<MetavariableId>,
        value: &ArgsCompoundView,
        data_arguments: &BTreeMap<String, Option<MetavariableId>>,
    ) -> bool {
        let Some(id) = id else { return false; };
        let metavariable = self.get(id);
        if metavariable.typename != *value.datatype().name() {
            return false;
        }
        match value.cases() {
            ArgsCompoundViewCases::Argument(argument) => {
                data_arguments.get(argument.name()).unwrap() == &Some(id)
            }
            ArgsCompoundViewCases::Constructor {
                constructor: required_constructor,
                arguments: required_constructor_arguments,
            } => {
                let Some(constructor) = &metavariable.constructor else { return false; };
                constructor.name == *required_constructor.name()
                    && required_constructor_arguments
                        .iter()
                        .enumerate()
                        .all(|(index, r)| {
                            self.metavariable_matches_datavalue(
                                *constructor
                                    .data_arguments
                                    .get(required_constructor.data_argument_indexed(index).name())
                                    .unwrap(),
                                r,
                                data_arguments,
                            )
                        })
            }
        }
    }
    pub fn local_validity(&self, id: MetavariableId) -> LocalValidity {
        let metavariable = self.get(id);
        let type_definition = COC.get(&metavariable.typename);
        let type_parameters_valid = zip(
            &metavariable.type_parameters,
            type_definition.type_parameters(),
        )
        .map(|(p, parameter_type)| match p {
            None => false,
            Some(other_id) => {
                let other = self.get(*other_id);
                other.typename == *parameter_type.name()
            }
        })
        .collect();
        let constructor_valid;
        let data_arguments_valid;
        let preconditions_valid;
        let return_type_parameters_valid;
        if let Some(constructor) = &metavariable.constructor {
            constructor_valid = true;

            let constructor_definition = type_definition.constructor(&constructor.name);
            data_arguments_valid = constructor_definition
                .data_arguments()
                .map(|argument_definition| {
                    let &a = constructor
                        .data_arguments
                        .get(argument_definition.name())
                        .unwrap();
                    (
                        argument_definition.name().to_owned(),
                        match a {
                            None => false,
                            Some(other_id) => {
                                let other = self.get(other_id);
                                other.typename == argument_definition.datatype().name()
                            }
                        },
                    )
                })
                .collect();

            preconditions_valid = zip(
                &constructor.preconditions,
                constructor_definition.preconditions(),
            )
            .map(|(p, precondition_definition)| match p {
                None => false,
                Some(other_id) => {
                    let other = self.get(*other_id);
                    if other.typename != *precondition_definition.predicate_type().name() {
                        return false;
                    }
                    zip(
                        &other.type_parameters,
                        precondition_definition.type_parameters(),
                    )
                    .all(|(&provided, needed)| {
                        self.metavariable_matches_datavalue(
                            provided,
                            &needed,
                            &constructor.data_arguments,
                        )
                    })
                }
            })
            .collect();

            return_type_parameters_valid = zip(
                constructor_definition.resulting_type_parameters(),
                &metavariable.type_parameters,
            )
            .map(|(provided, &needed)| {
                self.metavariable_matches_datavalue(needed, &provided, &constructor.data_arguments)
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

    pub fn set_data_argument(
        &mut self,
        id: MetavariableId,
        name: &str,
        value: Option<MetavariableId>,
    ) {
        let constructor = self.get_mut(id).constructor.as_mut().unwrap();
        *constructor.data_arguments.get_mut(name).unwrap() = value;
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

    pub fn metavariables(&self) -> &BTreeMap<MetavariableId, Metavariable> {
        &self.metavariables
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum CanMatch {
    Yes,
    Maybe,
    No,
}

impl Environment {
    pub fn fill_in_args_to_make_datavalue_match_metavariable(
        &self,
        id: Option<MetavariableId>,
        value: &ArgsCompoundView,
        data_arguments: &mut BTreeMap<String, Option<MetavariableId>>,
    ) -> CanMatch {
        let Some(id) = id else { return CanMatch::Maybe; };
        let metavariable = self.get(id);
        if metavariable.typename != *value.datatype().name() {
            return CanMatch::No;
        }
        match value.cases() {
            ArgsCompoundViewCases::Argument(argument) => {
                let arg = data_arguments.get_mut(argument.name()).unwrap();
                if arg.is_none() {
                    *arg = Some(id)
                }
                if *arg == Some(id) {
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
                let Some(constructor) = &metavariable.constructor else { return CanMatch::Maybe; };
                if constructor.name != *required_constructor.name() {
                    return CanMatch::No;
                }
                let mut submatch_results = CanMatch::Yes;
                for (r, a) in zip(
                    required_constructor_arguments,
                    required_constructor.data_arguments(),
                ) {
                    let submatch_possible = self.fill_in_args_to_make_datavalue_match_metavariable(
                        *constructor.data_arguments.get(a.name()).unwrap(),
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

    pub fn make_metavariable_that_matches_data_value(
        &mut self,
        value: &ArgsCompoundView,
        data_arguments: &mut BTreeMap<String, Option<MetavariableId>>,
    ) -> MetavariableId {
        if let Some(existing) = self
            .metavariables
            .keys()
            .copied()
            .find(|&id| self.metavariable_matches_datavalue(Some(id), value, data_arguments))
        {
            return existing;
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
                    self.set_data_argument(new_id, argument_definition.name(), Some(new_child_id));
                }
            }
        }
        new_id
    }

    pub fn constructor_possible(&self, id: MetavariableId, constructor_name: &str) -> CanMatch {
        let metavariable = self.get(id);

        let type_definition = COC.get(&metavariable.typename);
        let constructor_definition = type_definition.constructor(constructor_name);
        let mut data_arguments: BTreeMap<String, Option<MetavariableId>> = constructor_definition
            .data_arguments()
            .map(|a| (a.name().to_owned(), None))
            .collect();
        let mut match_results = CanMatch::Yes;
        for (&required, produced) in zip(
            &metavariable.type_parameters,
            constructor_definition.resulting_type_parameters(),
        ) {
            let match_possible = self.fill_in_args_to_make_datavalue_match_metavariable(
                required,
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
        let metavariable = self.get(id);

        let type_definition = COC.get(&metavariable.typename);

        if metavariable.constructor.is_none() {
            let mut possible_constructors: ArrayVec<&str, 2> = ArrayVec::new();
            for constructor in type_definition.constructors() {
                match self.constructor_possible(id, constructor.name()) {
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
        let metavariable = self.get(id);

        if let Some(constructor) = &metavariable.constructor {
            let constructor_definition = type_definition.constructor(&constructor.name);
            let mut data_arguments = constructor.data_arguments.clone();
            for (&defined, resulting) in zip(
                &metavariable.type_parameters,
                constructor_definition.resulting_type_parameters(),
            ) {
                self.fill_in_args_to_make_datavalue_match_metavariable(
                    defined,
                    &resulting,
                    &mut data_arguments,
                );
            }
            for (precondition_definition, &defined) in zip(
                constructor_definition.preconditions(),
                &constructor.preconditions,
            ) {
                if let Some(defined) = defined {
                    let other = self.get(defined);
                    for (required, &defined) in zip(
                        precondition_definition.type_parameters(),
                        &other.type_parameters,
                    ) {
                        self.fill_in_args_to_make_datavalue_match_metavariable(
                            defined,
                            &required,
                            &mut data_arguments,
                        );
                    }
                }
            }
            if data_arguments != constructor.data_arguments {
                self.get_mut(id)
                    .constructor
                    .as_mut()
                    .unwrap()
                    .data_arguments = data_arguments;
                return self.autofill(id);
            }

            for (precondition_index, (precondition_definition, &defined)) in zip(
                constructor_definition.preconditions(),
                &constructor.preconditions,
            )
            .enumerate()
            {
                if defined.is_none() {
                    // if there's already a metavariable that satisfies this, use it:
                    for (&other_id, other) in &self.metavariables {
                        let mut set_data_arg = None;
                        let typename = precondition_definition.predicate_type().name();
                        if other.typename == *typename
                            && zip(
                                    precondition_definition.type_parameters(),
                                    &other.type_parameters,
                            )
                            .enumerate()
                            .all(
                                |(index, (required, &provided))| {
                                    // certain parameters are "fully determined" by the other parameters,
                                    // so we count something as "matching" if we do not specify that parameter
                                    // TODO fix duplicate code id f9gd67fg8re8g
                                    if (typename == "FormulaSubstitution"
                                            || typename == "BindingSubstitution")
                                        && index == 3
                                    {
                                        let ArgsCompoundViewCases::Argument(argument) = required.cases() else {unreachable!()};
                                        if data_arguments[argument.name()].is_none() {
                                            set_data_arg = Some((argument.name(), other.type_parameters[index], typename));
                                            return true
                                        }
                                    }
                                    self.metavariable_matches_datavalue(
                                        provided,
                                        &required,
                                        &constructor.data_arguments,
                                    )
                                },
                            )
                        {
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

                    // If there's not one already ... create it!
                    let new_precondition_id = self.create_metavariable(
                        precondition_definition.predicate_type().name().to_owned(),
                    );
                    self.get_mut(id).constructor.as_mut().unwrap().preconditions
                        [precondition_index] = Some(new_precondition_id);
                    for (index, required) in precondition_definition.type_parameters().enumerate() {
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
