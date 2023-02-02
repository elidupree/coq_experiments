use crate::constructors::{Constructors, DataValue};
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
        value: &DataValue,
        datatype: &str,
        data_arguments: &BTreeMap<String, Option<MetavariableId>>,
    ) -> bool {
        let Some(id) = id else { return false; };
        let metavariable = self.get(id);
        if metavariable.typename != *datatype {
            return false;
        }
        let datatype = Constructors::coc().types.get(datatype).unwrap();
        match value {
            DataValue::Argument(argname) => data_arguments.get(argname).unwrap() == &Some(id),
            DataValue::Constructor {
                constructor: required_constructor_name,
                arguments: required_constructor_arguments,
            } => {
                let Some(constructor) = &metavariable.constructor else { return false; };
                let constructor_definition = datatype.constructors.get(&constructor.name).unwrap();
                constructor.name == *required_constructor_name
                    && zip(
                        required_constructor_arguments,
                        &constructor_definition.data_arguments,
                    )
                    .all(|(r, a)| {
                        self.metavariable_matches_datavalue(
                            *constructor.data_arguments.get(&a.name).unwrap(),
                            r,
                            &a.datatype,
                            data_arguments,
                        )
                    })
            }
        }
    }
    pub fn local_validity(&self, id: MetavariableId) -> LocalValidity {
        let metavariable = self.get(id);
        let type_definition = Constructors::coc()
            .types
            .get(&metavariable.typename)
            .unwrap();
        let type_parameters_valid = zip(
            &metavariable.type_parameters,
            &type_definition.type_parameters,
        )
        .map(|(p, parameter_type)| match p {
            None => false,
            Some(other_id) => {
                let other = self.get(*other_id);
                other.typename == *parameter_type
            }
        })
        .collect();
        let constructor_valid;
        let data_arguments_valid;
        let preconditions_valid;
        let return_type_parameters_valid;
        if let Some(constructor) = &metavariable.constructor {
            constructor_valid = true;

            let constructor_definition =
                type_definition.constructors.get(&constructor.name).unwrap();
            data_arguments_valid = constructor_definition
                .data_arguments
                .iter()
                .map(|argument_definition| {
                    let a = constructor
                        .data_arguments
                        .get(&argument_definition.name)
                        .unwrap();
                    (
                        argument_definition.name.clone(),
                        match a {
                            None => false,
                            Some(other_id) => {
                                let other = self.get(*other_id);
                                other.typename == argument_definition.datatype
                            }
                        },
                    )
                })
                .collect();

            preconditions_valid = zip(
                &constructor.preconditions,
                &constructor_definition.preconditions,
            )
            .map(|(p, precondition_definition)| match p {
                None => false,
                Some(other_id) => {
                    let other = self.get(*other_id);
                    if other.typename != precondition_definition.predicate_type {
                        return false;
                    }
                    let predicate_definition =
                        Constructors::coc().types.get(&other.typename).unwrap();
                    zip(
                        &other.type_parameters,
                        zip(
                            &precondition_definition.type_parameters,
                            &predicate_definition.type_parameters,
                        ),
                    )
                    .all(|(&provided, (needed, datatype))| {
                        self.metavariable_matches_datavalue(
                            provided,
                            needed,
                            datatype,
                            &constructor.data_arguments,
                        )
                    })
                }
            })
            .collect();

            return_type_parameters_valid = zip(
                &constructor_definition.resulting_type_parameters,
                zip(
                    &metavariable.type_parameters,
                    &type_definition.type_parameters,
                ),
            )
            .map(|(provided, (&needed, datatype))| {
                self.metavariable_matches_datavalue(
                    needed,
                    provided,
                    datatype,
                    &constructor.data_arguments,
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
        let type_definition = Constructors::coc().types.get(&typename).unwrap();
        self.metavariables.insert(
            id,
            Metavariable {
                name: "".to_string(),
                typename,
                type_parameters: type_definition
                    .type_parameters
                    .iter()
                    .map(|_| None)
                    .collect(),
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
        let type_definition = Constructors::coc()
            .types
            .get(&metavariable.typename)
            .unwrap();
        metavariable.constructor = value.map(|name| {
            let constructor = type_definition.constructors.get(&name).unwrap();
            MetavariableConstructor {
                name,
                data_arguments: constructor
                    .data_arguments
                    .iter()
                    .map(|a| (a.name.clone(), None))
                    .collect(),
                preconditions: constructor.preconditions.iter().map(|_| None).collect(),
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
        value: &DataValue,
        datatype: &str,
        data_arguments: &mut BTreeMap<String, Option<MetavariableId>>,
    ) -> CanMatch {
        let Some(id) = id else { return CanMatch::Maybe; };
        let metavariable = self.get(id);
        if metavariable.typename != *datatype {
            return CanMatch::No;
        }
        let datatype = Constructors::coc().types.get(datatype).unwrap();
        match value {
            DataValue::Argument(argname) => {
                let arg = data_arguments.get_mut(argname).unwrap();
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
            DataValue::Constructor {
                constructor: required_constructor_name,
                arguments: required_constructor_arguments,
            } => {
                let Some(constructor) = &metavariable.constructor else { return CanMatch::Maybe; };
                let constructor_definition = datatype.constructors.get(&constructor.name).unwrap();
                if constructor.name != *required_constructor_name {
                    return CanMatch::No;
                }
                let mut submatch_results = CanMatch::Yes;
                for (r, a) in zip(
                    required_constructor_arguments,
                    &constructor_definition.data_arguments,
                ) {
                    let submatch_possible = self.fill_in_args_to_make_datavalue_match_metavariable(
                        *constructor.data_arguments.get(&a.name).unwrap(),
                        r,
                        &a.datatype,
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
        value: &DataValue,
        datatype: &str,
        data_arguments: &mut BTreeMap<String, Option<MetavariableId>>,
    ) -> MetavariableId {
        if let Some(existing) = self.metavariables.keys().copied().find(|&id| {
            self.metavariable_matches_datavalue(Some(id), value, datatype, data_arguments)
        }) {
            return existing;
        }
        let new_id = self.create_metavariable(datatype.to_owned());
        let datatype = Constructors::coc().types.get(datatype).unwrap();
        match value {
            DataValue::Argument(argument) => {
                let existing = data_arguments.get_mut(argument).unwrap();
                assert!(
                    existing.is_none(),
                    "if it was Some then the variable it points to should have matched"
                );
                *existing = Some(new_id);
            }
            DataValue::Constructor {
                constructor,
                arguments,
            } => {
                let constructor_definition = datatype.constructors.get(constructor).unwrap();
                self.set_constructor(new_id, Some(constructor.clone()));
                for (child_value, argument_definition) in
                    zip(arguments, &constructor_definition.data_arguments)
                {
                    let new_child_id = self.make_metavariable_that_matches_data_value(
                        child_value,
                        &argument_definition.datatype,
                        data_arguments,
                    );
                    self.set_data_argument(new_id, &argument_definition.name, Some(new_child_id));
                }
            }
        }
        new_id
    }

    pub fn constructor_possible(&self, id: MetavariableId, constructor_name: &str) -> CanMatch {
        let metavariable = self.get(id);

        let type_definition = Constructors::coc()
            .types
            .get(&metavariable.typename)
            .unwrap();
        let constructor_definition = type_definition.constructors.get(constructor_name).unwrap();
        let mut data_arguments: BTreeMap<String, Option<MetavariableId>> = constructor_definition
            .data_arguments
            .iter()
            .map(|a| (a.name.clone(), None))
            .collect();
        let mut match_results = CanMatch::Yes;
        for (&required, (datatype, produced)) in zip(
            &metavariable.type_parameters,
            zip(
                &type_definition.type_parameters,
                &constructor_definition.resulting_type_parameters,
            ),
        ) {
            let match_possible = self.fill_in_args_to_make_datavalue_match_metavariable(
                required,
                produced,
                datatype,
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

        let type_definition = Constructors::coc()
            .types
            .get(&metavariable.typename)
            .unwrap();

        if metavariable.constructor.is_none() {
            let mut possible_constructors: ArrayVec<&String, 2> = ArrayVec::new();
            for constructor_name in type_definition.constructors.keys() {
                match self.constructor_possible(id, constructor_name) {
                    CanMatch::Yes => {
                        possible_constructors.clear();
                        possible_constructors.push(constructor_name);
                        break;
                    }
                    CanMatch::Maybe => {
                        let _ = possible_constructors.try_push(constructor_name);
                    }
                    CanMatch::No => {}
                }
            }
            if let &[only_constructor_name] = &*possible_constructors {
                self.set_constructor(id, Some(only_constructor_name.clone()));
            }
        }
        let metavariable = self.get(id);

        if let Some(constructor) = &metavariable.constructor {
            let constructor_definition =
                type_definition.constructors.get(&constructor.name).unwrap();
            let mut data_arguments = constructor.data_arguments.clone();
            for (typename, (&defined, resulting)) in zip(
                &type_definition.type_parameters,
                zip(
                    &metavariable.type_parameters,
                    &constructor_definition.resulting_type_parameters,
                ),
            ) {
                self.fill_in_args_to_make_datavalue_match_metavariable(
                    defined,
                    resulting,
                    typename,
                    &mut data_arguments,
                );
            }
            for (precondition_definition, &defined) in zip(
                &constructor_definition.preconditions,
                &constructor.preconditions,
            ) {
                if let Some(defined) = defined {
                    let other = self.get(defined);
                    let predicate_definition = Constructors::coc()
                        .types
                        .get(&precondition_definition.predicate_type)
                        .unwrap();
                    for (typename, (required, &defined)) in zip(
                        &predicate_definition.type_parameters,
                        zip(
                            &precondition_definition.type_parameters,
                            &other.type_parameters,
                        ),
                    ) {
                        self.fill_in_args_to_make_datavalue_match_metavariable(
                            defined,
                            required,
                            typename,
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
                &constructor_definition.preconditions,
                &constructor.preconditions,
            )
            .enumerate()
            {
                if defined.is_none() {
                    let predicate_definition = Constructors::coc()
                        .types
                        .get(&precondition_definition.predicate_type)
                        .unwrap();
                    // if there's already a metavariable that satisfies this, use it:
                    for (&other_id, other) in &self.metavariables {
                        let mut set_data_arg = None;
                        if other.typename == precondition_definition.predicate_type
                            && zip(
                                &predicate_definition.type_parameters,
                                zip(
                                    &precondition_definition.type_parameters,
                                    &other.type_parameters,
                                ),
                            )
                            .enumerate()
                            .all(
                                |(index, (typename, (required, &provided)))| {
                                    // certain parameters are "fully determined" by the other parameters,
                                    // so we count something as "matching" if we do not specify that parameter
                                    // TODO fix duplicate code id f9gd67fg8re8g
                                    if (typename == "FormulaSubstitution"
                                            || typename == "BindingSubstitution")
                                        && index == 3
                                    {
                                        let DataValue::Argument(name) = &required else {unreachable!()};
                                        if data_arguments[name].is_none() {
                                            set_data_arg = Some((name.clone(), other.type_parameters[index], typename.clone()));
                                            return true
                                        }
                                    }
                                    self.metavariable_matches_datavalue(
                                        provided,
                                        required,
                                        typename,
                                        &constructor.data_arguments,
                                    )
                                },
                            )
                        {
                            self.get_mut(id).constructor.as_mut().unwrap().preconditions
                                [precondition_index] = Some(other_id);
                            if let Some((argname, existing, typename)) = set_data_arg{
                                let new_id = existing.unwrap_or_else(|| {
                                    let new_id = self.create_metavariable(typename);
                                    // TODO fix duplicate code id f9gd67fg8re8g
                                    self.get_mut(other_id).type_parameters[3] = Some(new_id);
                                    new_id
                                });
                                *self.get_mut(id).constructor.as_mut().unwrap().data_arguments.get_mut (&argname).unwrap() = Some (new_id);
                            }
                            return self.autofill(id);
                        }
                    }

                    // If there's not one already ... create it!
                    let new_precondition_id =
                        self.create_metavariable(precondition_definition.predicate_type.clone());
                    self.get_mut(id).constructor.as_mut().unwrap().preconditions
                        [precondition_index] = Some(new_precondition_id);
                    for (index, (typename, required)) in zip(
                        &predicate_definition.type_parameters,
                        &precondition_definition.type_parameters,
                    )
                    .enumerate()
                    {
                        let new_parameter_id = self.make_metavariable_that_matches_data_value(
                            required,
                            typename,
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
