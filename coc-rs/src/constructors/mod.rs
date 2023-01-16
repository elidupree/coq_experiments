use live_prop_test::{lpt_assert, lpt_assert_eq};
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::iter::zip;

#[allow(clippy::all)]
mod lalrpop_wrapper {
    use lalrpop_util::lalrpop_mod;
    lalrpop_mod!(pub(crate) constructors, "/constructors/constructors.rs");
}

pub use self::lalrpop_wrapper::constructors::ConstructorsParser;

#[derive(Debug)]
pub struct DataArgument {
    pub name: String,
    pub datatype: String,
}

#[derive(Debug)]
pub enum DataValue {
    Argument(String),
    Constructor {
        constructor: String,
        arguments: Vec<DataValue>,
    },
}

#[derive(Debug)]
pub struct Precondition {
    pub predicate_type: String,
    pub type_parameters: Vec<DataValue>,
}

#[derive(Debug)]
pub struct DataTypeConstructor {
    pub arguments: Vec<DataArgument>,
    pub notation: String,
}

#[derive(Debug)]
pub struct PredicateTypeConstructor {
    pub data_arguments: Vec<DataArgument>,
    pub preconditions: Vec<Precondition>,
    pub resulting_type_parameters: Vec<DataValue>,
}

#[derive(Debug)]
pub struct DataType {
    pub constructors: BTreeMap<String, DataTypeConstructor>,
}

#[derive(Debug)]
pub struct PredicateType {
    pub type_parameters: Vec<String>,
    pub notation: String,
    pub constructors: BTreeMap<String, PredicateTypeConstructor>,
}

#[derive(Debug)]
pub struct Constructors {
    pub datatypes: BTreeMap<String, DataType>,
    pub predicate_types: BTreeMap<String, PredicateType>,
}

#[derive(Debug)]
pub(crate) enum ConstructorEntry {
    DataType {
        name: String,
    },
    PredicateType {
        name: String,
        type_parameters: Vec<String>,
        notation: String,
    },
    Constructor {
        name: String,
        constructed_type: String,
        data_arguments: Vec<DataArgument>,
        preconditions: Vec<Precondition>,
        resulting_type_parameters: Vec<DataValue>,
        notation: Option<String>,
    },
}

impl Default for Constructors {
    fn default() -> Self {
        Constructors {
            datatypes: Default::default(),
            predicate_types: Default::default(),
        }
    }
}

impl Constructors {
    pub fn coc() -> Self {
        ConstructorsParser::new()
            .parse(include_str!("coc.constructors"))
            .unwrap()
    }

    pub(crate) fn add_entry(&mut self, entry: ConstructorEntry) -> Result<(), String> {
        match entry {
            ConstructorEntry::DataType { name } => {
                self.datatypes.insert(
                    name,
                    DataType {
                        constructors: Default::default(),
                    },
                );
                Ok(())
            }
            ConstructorEntry::PredicateType {
                name,
                type_parameters,
                notation,
            } => {
                self.predicate_types.insert(
                    name,
                    PredicateType {
                        type_parameters,
                        notation,
                        constructors: Default::default(),
                    },
                );
                Ok(())
            }
            ConstructorEntry::Constructor {
                name,
                constructed_type,
                data_arguments,
                preconditions,
                resulting_type_parameters,
                notation,
            } => {
                if let Some(datatype) = self.datatypes.get_mut(&constructed_type) {
                    let notation = notation.ok_or_else(|| {
                        format!(
                            "Constructor {} for data type {} needs a notation",
                            name, constructed_type
                        )
                    })?;
                    if !preconditions.is_empty() {
                        return Err(format!(
                            "Constructor {} for data type {} can't have precondition",
                            name, constructed_type,
                        ));
                    }
                    if !resulting_type_parameters.is_empty() {
                        return Err(format!(
                            "Constructor {} for data type {} can't have resulting type parameters",
                            name, constructed_type,
                        ));
                    }
                    let old_value = datatype.constructors.insert(
                        name.clone(),
                        DataTypeConstructor {
                            arguments: data_arguments,
                            notation,
                        },
                    );
                    if old_value.is_some() {
                        return Err(format!(
                            "Duplicate definition of constructor {} for data type {}",
                            name, constructed_type,
                        ));
                    }
                    Ok(())
                } else if let Some(predicate_type) = self.predicate_types.get_mut(&constructed_type)
                {
                    if notation.is_some() {
                        return Err(format!(
                            "Constructor {} for predicate type {} can't have a notation (for now at least)",
                            name, constructed_type
                        ));
                    }
                    if resulting_type_parameters.len() != predicate_type.type_parameters.len() {
                        return Err(format!(
                            "Constructor {} for predicate type {} has wrong number of resulting type parameters (found {}, needs {})",
                            name, constructed_type, resulting_type_parameters.len(), predicate_type.type_parameters.len()
                        ));
                    }
                    let old_value = predicate_type.constructors.insert(
                        name.clone(),
                        PredicateTypeConstructor {
                            data_arguments,
                            preconditions,
                            resulting_type_parameters,
                        },
                    );
                    if old_value.is_some() {
                        return Err(format!(
                            "Duplicate definition of constructor {} for data type {}",
                            name, constructed_type,
                        ));
                    }

                    Ok(())
                } else {
                    Err(format!(
                        "Defining constructor for nonexistent type {}",
                        constructed_type
                    ))
                }
            }
        }
    }

    pub fn notation_regex() -> Regex {
        Regex::new(r#"\{([^{}]*)\}"#).unwrap()
    }

    pub fn check_invariants(&self) -> Result<(), String> {
        let regex = Self::notation_regex();
        let mut global_names = HashSet::new();
        let mut observe_global_name = |name: &str| {
            lpt_assert!(
                global_names.insert(name.to_string()),
                "Duplicate global name: {}",
                name
            );
            Ok(())
        };
        for (datatype_name, datatype) in &self.datatypes {
            observe_global_name(datatype_name)?;
            for (constructor_name, constructor) in &datatype.constructors {
                observe_global_name(constructor_name)?;
                let mut arguments_map = HashSet::new();
                for argument in &constructor.arguments {
                    lpt_assert!(
                        arguments_map.insert(&*argument.name),
                        "Duplicate argument: {}",
                        argument.name
                    );

                    lpt_assert!(
                        self.datatypes.contains_key(&argument.datatype),
                        "Constructor {} takes parameter of non-existent datatype {}",
                        constructor_name,
                        argument.datatype,
                    );
                }
                for captures in regex.captures_iter(&constructor.notation) {
                    let format_name = captures.get(1).unwrap().as_str();
                    lpt_assert!(
                        arguments_map.contains(format_name),
                        "Notation {} of constructor {} expected argument {}, which isn't present",
                        constructor.notation,
                        constructor_name,
                        format_name
                    );
                }
            }
        }
        for (predicate_name, predicate) in &self.predicate_types {
            observe_global_name(predicate_name)?;
            for type_parameter in &predicate.type_parameters {
                lpt_assert!(
                    self.datatypes.contains_key(type_parameter),
                    "Predicate {} takes parameter of non-existent datatype {}",
                    predicate_name,
                    type_parameter,
                );
            }
            let notation_capture_indices = regex.captures_iter(&predicate.notation).map(|captures| {
                let capture_str = captures.get(1).unwrap().as_str();
                capture_str.parse::<usize>().map_err(|_| format!("Notation {} for predicate {} tried to capture {}, which isn't a numeric index", predicate.notation, predicate_name, capture_str))
            }).collect::<Result<BTreeSet<usize>, String>>()?;
            let type_parameter_indices =
                (0..predicate.type_parameters.len()).collect::<BTreeSet<usize>>();
            lpt_assert_eq!(
                notation_capture_indices,
                type_parameter_indices,
                "Notation {} for predicate {} didn't capture the right set of indices",
                predicate.notation,
                predicate_name
            );

            for (constructor_name, constructor) in &predicate.constructors {
                observe_global_name(constructor_name)?;
                let mut arguments_map = HashMap::new();
                for argument in &constructor.data_arguments {
                    lpt_assert!(
                        arguments_map
                            .insert(&argument.name, &argument.datatype)
                            .is_none(),
                        "Duplicate argument: {}",
                        argument.name
                    );

                    lpt_assert!(
                        self.datatypes.contains_key(&argument.datatype),
                        "Constructor {} takes parameter of non-existent datatype {}",
                        constructor_name,
                        argument.datatype,
                    );
                }
                fn value_must_be_type(
                    value: &DataValue,
                    datatype: &String,
                    constructor_name: &String,
                    arguments_map: &HashMap<&String, &String>,
                    datatypes: &BTreeMap<String, DataType>,
                ) -> Result<(), String> {
                    match value {
                        DataValue::Argument(argument_name) => {
                            let Some(&argument_type) = arguments_map.get(argument_name) else { return Err(format!("In constructor {}, tried to reference nonexistent argument {}", constructor_name, argument_name)); };
                            lpt_assert_eq!(argument_type, datatype);
                            Ok(())
                        }
                        DataValue::Constructor {
                            constructor: datatype_constructor_name,
                            arguments,
                        } => {
                            let Some(datatype_constructor) = datatypes.get(datatype).unwrap().constructors.get(datatype_constructor_name) else { return Err(format!("In constructor {}, tried to reference nonexistent constructor {}", constructor_name, datatype_constructor_name)); };

                            lpt_assert_eq!(
                                arguments.len(),
                                datatype_constructor.arguments.len(),
                                "In constructor {}, gave wrong number of arguments to constructor {}",
                                constructor_name,
                                datatype_constructor_name,
                            );
                            for (value, constructor_argument) in
                                zip(arguments, &datatype_constructor.arguments)
                            {
                                value_must_be_type(
                                    value,
                                    &constructor_argument.datatype,
                                    constructor_name,
                                    arguments_map,
                                    datatypes,
                                )?;
                            }

                            Ok(())
                        }
                    }
                }
                for precondition in &constructor.preconditions {
                    let Some(precondition_type) = self.predicate_types.get(&precondition.predicate_type) else {
                        return Err(format!("Constructor {} takes parameter of non-existent predicate {}",
                                           constructor_name,
                                           precondition.predicate_type, ));
                    };
                    lpt_assert_eq!(
                        precondition.type_parameters.len(),
                        precondition_type.type_parameters.len(),
                        "Precondition {:?} for constructor {} didn't have the right number of type parameters",
                        precondition,
                        constructor_name,
                    );
                    for (value, datatype) in zip(
                        &precondition.type_parameters,
                        &precondition_type.type_parameters,
                    ) {
                        value_must_be_type(
                            value,
                            datatype,
                            constructor_name,
                            &arguments_map,
                            &self.datatypes,
                        )?;
                    }

                    //precondition.type_parameters.
                }
                lpt_assert_eq!(
                    constructor.resulting_type_parameters.len(),
                    predicate.type_parameters.len(),
                    "Constructor {} has wrong number of resulting type parameters",
                    constructor_name,
                );
                for (resulting_type_parameter, type_parameter) in zip(
                    &constructor.resulting_type_parameters,
                    &predicate.type_parameters,
                ) {
                    value_must_be_type(
                        resulting_type_parameter,
                        type_parameter,
                        constructor_name,
                        &arguments_map,
                        &self.datatypes,
                    )?;
                }
            }
        }

        Ok(())
    }
}

#[test]
fn coc_constructors_valid() {
    Constructors::coc().check_invariants().unwrap()
}
