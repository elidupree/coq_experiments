use live_prop_test::{lpt_assert, lpt_assert_eq};
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::iter::zip;
use std::sync::LazyLock;

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
pub struct Constructor {
    pub data_arguments: Vec<DataArgument>,
    pub preconditions: Vec<Precondition>,
    pub resulting_type_parameters: Vec<DataValue>,
    pub notation: Option<Notation<String>>,
}

#[derive(Debug)]
pub struct TypeDefinition {
    pub type_parameters: Vec<String>,
    pub notation: Notation<usize>,
    pub constructors: BTreeMap<String, Constructor>,
}

#[derive(Default, Debug)]
pub struct Constructors {
    pub types: BTreeMap<String, TypeDefinition>,
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

#[derive(Debug)]
pub enum NotationItem<T> {
    Text(String),
    Argument(T),
}

#[derive(Debug)]
pub enum NotationMapItem<'a, T> {
    Text(&'a String),
    Argument(T),
}

#[derive(Debug)]
pub struct Notation<T> {
    pub items: Vec<NotationItem<T>>,
}

impl<T> Notation<T> {
    pub fn try_from_str<E>(
        text: &str,
        mut argument_function: impl FnMut(&str) -> Result<T, E>,
    ) -> Result<Self, E> {
        let mut items: Vec<NotationItem<T>> = Vec::new();
        let mut rest = text;
        while let Some(captures) = Constructors::notation_regex().captures(rest) {
            let before = &rest[..captures.get(0).unwrap().start()];
            if !before.is_empty() {
                items.push(NotationItem::Text(before.to_owned()));
            }
            items.push(NotationItem::Argument(argument_function(
                captures.get(1).unwrap().as_str(),
            )?));
            rest = &rest[captures.get(0).unwrap().end()..];
        }
        if !rest.is_empty() {
            items.push(NotationItem::Text(rest.to_owned()));
        }
        Ok(Notation { items })
    }
    // pub fn map<'a, U>(
    //     &'a self,
    //     mut argument_function: impl FnMut(&T) -> U + 'a,
    // ) -> impl Iterator<Item = NotationMapItem<'a, U>> + 'a {
    //     self.items.iter().map(move |item| match item {
    //         NotationItem::Text(text) => NotationMapItem::Text(text),
    //         NotationItem::Argument(argument) => {
    //             NotationMapItem::Argument(argument_function(argument))
    //         }
    //     })
    // }
}

impl Constructors {
    pub fn coc() -> &'static Self {
        static COC: LazyLock<Constructors> = LazyLock::new(|| {
            ConstructorsParser::new()
                .parse(include_str!("coc.constructors"))
                .unwrap()
        });
        &COC
    }

    pub(crate) fn add_entry(&mut self, entry: ConstructorEntry) -> Result<(), String> {
        match entry {
            ConstructorEntry::DataType { name } => {
                self.types.insert(
                    name.clone(),
                    TypeDefinition {
                        type_parameters: Vec::new(),
                        notation: Notation {
                            items: vec![NotationItem::Text(name)],
                        },
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
                let notation = Notation::try_from_str(&notation, |argument| {
                    let index = argument.parse::<usize>().map_err(|_| format!("Notation {} for predicate {} tried to capture {}, which isn't a numeric index", notation, name, argument))?;
                    if type_parameters.get(index).is_none() {
                        Err(format!("Notation {} for predicate {} tried to capture index {}, which is too big for the number of type parameters", notation, name, index))
                    } else {
                        Ok(index)
                    }
                })?;
                self.types.insert(
                    name,
                    TypeDefinition {
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
                if let Some(type_definition) = self.types.get_mut(&constructed_type) {
                    if resulting_type_parameters.len() != type_definition.type_parameters.len() {
                        return Err(format!(
                            "Constructor {} for type {} has wrong number of resulting type parameters (found {}, needs {})",
                            name, constructed_type, resulting_type_parameters.len(), type_definition.type_parameters.len()
                        ));
                    }
                    let notation = match notation {
                        None => None,
                        Some(notation) => {
                            Some(Notation::try_from_str(&notation, |argument_name| {
                                if data_arguments.iter().any(|a| a.name == argument_name) {
                                    Ok(argument_name.to_owned())
                                } else {
                                    Err(format!("Notation {:?} of constructor {} expected data-argument {}, which isn't present",
                                                notation,
                                                name,
                                                argument_name))
                                }
                            })?)
                        }
                    };

                    let old_value = type_definition.constructors.insert(
                        name.clone(),
                        Constructor {
                            data_arguments,
                            preconditions,
                            resulting_type_parameters,
                            notation,
                        },
                    );
                    if old_value.is_some() {
                        return Err(format!(
                            "Duplicate definition of constructor {} for type {}",
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

    fn notation_regex() -> Regex {
        Regex::new(r#"\{([^{}]*)\}"#).unwrap()
    }

    pub fn check_invariants(&self) -> Result<(), String> {
        let mut global_names = HashSet::new();
        let mut observe_global_name = |name: &str| {
            lpt_assert!(
                global_names.insert(name.to_string()),
                "Duplicate global name: {}",
                name
            );
            Ok(())
        };
        for (typename, type_definition) in &self.types {
            observe_global_name(typename)?;
            for type_parameter in &type_definition.type_parameters {
                let Some(datatype) = self.types.get(type_parameter) else {
                    return Err(format!("Predicate {} takes parameter of non-existent datatype {}",
                                       typename,
                                       type_parameter));
                };
                lpt_assert!(
                    datatype.type_parameters.is_empty(),
                    "Predicate {} takes parameter of predicate {}",
                    typename,
                    type_parameter
                );
            }

            let notation_capture_indices = type_definition
                .notation
                .items
                .iter()
                .filter_map(|item| {
                    if let &NotationItem::Argument(index) = item {
                        Some(index)
                    } else {
                        None
                    }
                })
                .collect::<BTreeSet<usize>>();
            let type_parameter_indices =
                (0..type_definition.type_parameters.len()).collect::<BTreeSet<usize>>();
            lpt_assert_eq!(
                notation_capture_indices,
                type_parameter_indices,
                "Notation {:?} for predicate {} didn't capture the right set of indices",
                type_definition.notation,
                typename
            );

            for (constructor_name, constructor) in &type_definition.constructors {
                observe_global_name(constructor_name)?;
                let mut arguments_map: HashMap<&str, &str> = HashMap::new();
                for argument in &constructor.data_arguments {
                    lpt_assert!(
                        arguments_map
                            .insert(&argument.name, &argument.datatype)
                            .is_none(),
                        "Duplicate argument: {}",
                        argument.name
                    );

                    let Some(datatype) = self.types.get(&argument.datatype) else {
                        return Err(format!("Constructor {} takes parameter of non-existent datatype {}",
                                           constructor_name,
                                           argument.datatype));
                    };
                    lpt_assert!(
                        datatype.type_parameters.is_empty(),
                        "Constructor {} takes data-argument of predicate {}",
                        constructor_name,
                        argument.datatype
                    );
                }

                for precondition in &constructor.preconditions {
                    let Some(precondition_type) = self.types.get(&precondition.predicate_type) else {
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
                            &self.types,
                        )?;
                    }

                    //precondition.type_parameters.
                }
                lpt_assert_eq!(
                    constructor.resulting_type_parameters.len(),
                    type_definition.type_parameters.len(),
                    "Constructor {} has wrong number of resulting type parameters",
                    constructor_name,
                );
                for (resulting_type_parameter, type_parameter) in zip(
                    &constructor.resulting_type_parameters,
                    &type_definition.type_parameters,
                ) {
                    value_must_be_type(
                        resulting_type_parameter,
                        type_parameter,
                        constructor_name,
                        &arguments_map,
                        &self.types,
                    )?;
                }
                if let Some(notation) = &constructor.notation {
                    for item in &notation.items {
                        if let NotationItem::Argument(argument_name) = item {
                            lpt_assert!(
                            arguments_map.contains_key(&**argument_name),
                            "Notation {:?} of constructor {} expected data-argument {}, which isn't present",
                            notation,
                            constructor_name,
                            argument_name
                        );
                        }
                    }
                }
            }
        }

        Ok(())
    }
}

fn value_must_be_type(
    value: &DataValue,
    datatype_name: &str,
    constructor_name: &str,
    arguments_map: &HashMap<&str, &str>,
    types: &BTreeMap<String, TypeDefinition>,
) -> Result<(), String> {
    match value {
        DataValue::Argument(argument_name) => {
            let Some(&argument_type) = arguments_map.get(&**argument_name) else { return Err(format!("In constructor {}, tried to reference nonexistent argument {}", constructor_name, argument_name)); };
            lpt_assert_eq!(
                argument_type,
                datatype_name,
                "Constructor {} tried to pass value as wrong datatype",
                constructor_name,
            );
            Ok(())
        }
        DataValue::Constructor {
            constructor: datatype_constructor_name,
            arguments,
        } => {
            let datatype = types.get(datatype_name).unwrap();
            let Some(datatype_constructor) = datatype.constructors.get(datatype_constructor_name) else { return Err(format!("In constructor {}, tried to reference nonexistent constructor {}", constructor_name, datatype_constructor_name)); };
            lpt_assert!(
                datatype.type_parameters.is_empty(),
                "Constructor {} takes data-argument of predicate {}",
                constructor_name,
                datatype_name
            );

            lpt_assert_eq!(
                arguments.len(),
                datatype_constructor.data_arguments.len(),
                "In constructor {}, gave wrong number of arguments to constructor {}",
                constructor_name,
                datatype_constructor_name,
            );

            lpt_assert!(
                datatype_constructor.preconditions.is_empty(),
                "In constructor {}, called constructor with preconditions {}",
                constructor_name,
                datatype_constructor_name,
            );
            for (value, constructor_argument) in
                zip(arguments, &datatype_constructor.data_arguments)
            {
                value_must_be_type(
                    value,
                    &constructor_argument.datatype,
                    constructor_name,
                    arguments_map,
                    types,
                )?;
            }

            Ok(())
        }
    }
}

#[test]
fn coc_constructors_valid() {
    Constructors::coc().check_invariants().unwrap()
}
