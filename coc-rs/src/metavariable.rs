use crate::constructors::{Constructors, DataValue};
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
    pub fn locally_valid(&self, id: MetavariableId) -> LocalValidity {
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
            data_arguments_valid = zip(
                constructor.data_arguments.values(),
                &constructor_definition.data_arguments,
            )
            .map(|(a, argument_definition)| {
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

    pub fn replace_constructor(&mut self, id: MetavariableId, value: Option<String>) {
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

    pub fn metavariables(&self) -> impl Iterator<Item = (&MetavariableId, &Metavariable)> {
        self.metavariables.iter()
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
