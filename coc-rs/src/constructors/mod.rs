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

// We have a bunch of "definition types" with corresponding "view types", where the view types provide a convenience for other code

#[derive(Debug)]
pub struct DataArgumentDefinition {
    pub name: String,
    pub datatype: String,
}

#[derive(Copy, Clone, Debug)]
pub struct DataArgumentView<'a> {
    index: usize,
    definition: &'a DataArgumentDefinition,
    constructor_view: ConstructorView<'a>,
}

#[derive(Debug)]
pub enum ArgsCompoundDefinition {
    Argument(String),
    Constructor {
        constructor: String,
        arguments: Vec<ArgsCompoundDefinition>,
    },
}

#[derive(Copy, Clone, Debug)]
pub struct ArgsCompoundView<'a> {
    datatype: &'a str,
    definition: &'a ArgsCompoundDefinition,
    constructor_view: ConstructorView<'a>,
}

#[derive(Debug)]
pub enum ArgsCompoundViewCases<'a> {
    Argument(DataArgumentView<'a>),
    Constructor {
        constructor: ConstructorView<'a>,
        arguments: Vec<ArgsCompoundView<'a>>,
    },
}

#[derive(Debug)]
pub struct PreconditionDefinition {
    pub predicate_type: String,
    pub type_parameters: Vec<ArgsCompoundDefinition>,
}

#[derive(Copy, Clone, Debug)]
pub struct PreconditionView<'a> {
    index: usize,
    definition: &'a PreconditionDefinition,
    constructor_view: ConstructorView<'a>,
}

#[derive(Debug)]
pub struct ConstructorDefinition {
    pub data_arguments: Vec<DataArgumentDefinition>,
    pub preconditions: Vec<PreconditionDefinition>,
    pub resulting_type_parameters: Vec<ArgsCompoundDefinition>,
    pub notation: Option<Notation<String>>,
}

#[derive(Copy, Clone, Debug)]
pub struct ConstructorView<'a> {
    name: &'a str,
    definition: &'a ConstructorDefinition,
    type_view: TypeView<'a>,
}

#[derive(Debug)]
pub struct TypeDefinition {
    pub type_parameters: Vec<String>,
    pub notation: Notation<usize>,
    pub constructors: BTreeMap<String, ConstructorDefinition>,
}

#[derive(Copy, Clone, Debug)]
pub struct TypeView<'a> {
    name: &'a str,
    definition: &'a TypeDefinition,
    constructors: &'a Constructors,
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
        data_arguments: Vec<DataArgumentDefinition>,
        preconditions: Vec<PreconditionDefinition>,
        resulting_type_parameters: Vec<ArgsCompoundDefinition>,
        notation: Option<String>,
    },
}

#[derive(Debug)]
pub enum NotationItem<T> {
    Text(String),
    Argument(T),
}

// #[derive(Debug)]
// pub enum NotationMapItem<'a, T> {
//     Text(&'a String),
//     Argument(T),
// }

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

impl<'a> DataArgumentView<'a> {
    pub fn index(&self) -> usize {
        self.index
    }
    pub fn name(&self) -> &'a str {
        &self.definition.name
    }
    pub fn typename(&self) -> &'a str {
        &self.definition.datatype
    }
    pub fn datatype(&self) -> TypeView<'a> {
        self.constructor_view
            .type_view
            .constructors
            .get(&self.definition.datatype)
    }
}

impl<'a> ArgsCompoundView<'a> {
    pub fn datatype(&self) -> TypeView<'a> {
        self.constructor_view
            .type_view
            .constructors
            .get(self.datatype)
    }
    pub fn cases(&self) -> ArgsCompoundViewCases<'a> {
        match self.definition {
            ArgsCompoundDefinition::Argument(argument) => {
                ArgsCompoundViewCases::Argument(self.constructor_view.data_argument_named(argument))
            }
            ArgsCompoundDefinition::Constructor {
                constructor,
                arguments,
            } => {
                let constructor = self.datatype().constructor(constructor);
                ArgsCompoundViewCases::Constructor {
                    constructor,
                    arguments: zip(arguments, &constructor.definition.data_arguments)
                        .map(|(argument, argument_definition)| ArgsCompoundView {
                            datatype: &argument_definition.datatype,
                            definition: argument,
                            constructor_view: self.constructor_view,
                        })
                        .collect(),
                }
            }
        }
    }
}

impl<'a> PreconditionView<'a> {
    pub fn index(&self) -> usize {
        self.index
    }
    pub fn predicate_type(&self) -> TypeView<'a> {
        self.constructor_view
            .type_view
            .constructors
            .get(&self.definition.predicate_type)
    }
    pub fn type_parameters(&self) -> impl Iterator<Item = ArgsCompoundView<'a>> + '_ {
        zip(
            &self.definition.type_parameters,
            &self.predicate_type().definition.type_parameters,
        )
        .map(|(parameter, datatype)| ArgsCompoundView {
            datatype,
            definition: parameter,
            constructor_view: self.constructor_view,
        })
    }
    pub fn type_parameter(&self, index: usize) -> ArgsCompoundView<'a> {
        let (Some(parameter), Some(datatype)) = (self.definition.type_parameters.get(index), self.predicate_type().definition.type_parameters.get(index)) else {
            panic!("Tried to get nonexistent type parameter {index} of precondition {} of constructor {}", self.index, self.constructor_view.name)
        };
        ArgsCompoundView {
            datatype,
            definition: parameter,
            constructor_view: self.constructor_view,
        }
    }
}

impl<'a> ConstructorView<'a> {
    pub fn name(&self) -> &'a str {
        self.name
    }
    pub fn notation(&self) -> Option<&'a Notation<String>> {
        self.definition.notation.as_ref()
    }
    pub fn data_arguments(&self) -> impl Iterator<Item = DataArgumentView<'a>> + 'a {
        let constructor_view = *self;
        self.definition
            .data_arguments
            .iter()
            .enumerate()
            .map(move |(index, argument)| DataArgumentView {
                index,
                definition: argument,
                constructor_view,
            })
    }
    pub fn data_argument_indexed(&self, index: usize) -> DataArgumentView<'a> {
        let Some (argument) = self.definition.data_arguments.get(index) else {
            panic!("Tried to get nonexistent data argument {index} of constructor {}", self.name)
        };
        DataArgumentView {
            index,
            definition: argument,
            constructor_view: *self,
        }
    }
    pub fn data_argument_named(&self, name: &str) -> DataArgumentView<'a> {
        let Some (index) = self.definition.data_arguments.iter().position(|argument |argument.name == name) else {
            panic!("Tried to get nonexistent data argument {name} of constructor {}", self.name)
        };
        DataArgumentView {
            index,
            definition: &self.definition.data_arguments[index],
            constructor_view: *self,
        }
    }
    pub fn preconditions(&self) -> impl Iterator<Item = PreconditionView<'a>> + 'a {
        let constructor_view = *self;
        self.definition
            .preconditions
            .iter()
            .enumerate()
            .map(move |(index, precondition)| PreconditionView {
                index,
                definition: precondition,
                constructor_view,
            })
    }
    pub fn precondition(&self, index: usize) -> PreconditionView<'a> {
        let Some (precondition) = self.definition.preconditions.get(index) else {
            panic!("Tried to get nonexistent precondition {index} of constructor {}", self.name)
        };
        PreconditionView {
            index,
            definition: precondition,
            constructor_view: *self,
        }
    }
    pub fn resulting_type_parameters(&self) -> impl Iterator<Item = ArgsCompoundView<'a>> + '_ {
        zip(
            &self.definition.resulting_type_parameters,
            &self.type_view.definition.type_parameters,
        )
        .map(|(parameter, datatype)| ArgsCompoundView {
            datatype,
            definition: parameter,
            constructor_view: *self,
        })
    }
    pub fn resulting_type_parameter(&self, index: usize) -> ArgsCompoundView<'a> {
        let (Some(parameter), Some(datatype)) = (self.definition.resulting_type_parameters.get(index), self.type_view.definition.type_parameters.get(index)) else {
            panic!("Tried to get nonexistent resulting-type-parameter {index} of constructor {}", self.name)
        };
        ArgsCompoundView {
            datatype,
            definition: parameter,
            constructor_view: *self,
        }
    }
}

impl<'a> TypeView<'a> {
    pub fn name(&self) -> &'a str {
        self.name
    }
    pub fn type_parameters(&self) -> impl Iterator<Item = TypeView<'a>> + '_ {
        self.definition
            .type_parameters
            .iter()
            .map(|typename| self.constructors.get(typename))
    }
    pub fn type_parameter(&self, index: usize) -> TypeView<'a> {
        let Some (typename) = self.definition.type_parameters.get(index) else {
            panic!("Tried to get nonexistent type parameter {index} of type {}", self.name)
        };
        self.constructors.get(typename)
    }
    pub fn constructors(&self) -> impl Iterator<Item = ConstructorView<'a>> + '_ {
        self.definition
            .constructors
            .iter()
            .map(|(name, definition)| ConstructorView {
                name,
                definition,
                type_view: *self,
            })
    }
    pub fn notation(&self) -> &'a Notation<usize> {
        &self.definition.notation
    }
    pub fn constructor(&self, name: &str) -> ConstructorView<'a> {
        let Some ((name, definition)) = self.definition.constructors.get_key_value(name) else {
            panic!("Tried to get nonexistent constructor {name} of type {}", self.name)
        };
        ConstructorView {
            name,
            definition,
            type_view: *self,
        }
    }
}

pub static COC: LazyLock<Constructors> = LazyLock::new(|| {
    ConstructorsParser::new()
        .parse(include_str!("coc.constructors"))
        .unwrap()
});

impl Constructors {
    pub fn coc() -> &'static Self {
        &COC
    }

    pub fn get(&self, typename: &str) -> TypeView {
        let Some ((name, definition)) = self.types.get_key_value(typename) else {
            panic!("Tried to get nonexistent type `{typename}`")
        };
        TypeView {
            name,
            definition,
            constructors: self,
        }
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
                        ConstructorDefinition {
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
                        "Constructor {:?} for constructor {} didn't have the right number of type parameters",
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
    value: &ArgsCompoundDefinition,
    datatype_name: &str,
    constructor_name: &str,
    arguments_map: &HashMap<&str, &str>,
    types: &BTreeMap<String, TypeDefinition>,
) -> Result<(), String> {
    match value {
        ArgsCompoundDefinition::Argument(argument_name) => {
            let Some(&argument_type) = arguments_map.get(&**argument_name) else { return Err(format!("In constructor {}, tried to reference nonexistent argument {}", constructor_name, argument_name)); };
            lpt_assert_eq!(
                argument_type,
                datatype_name,
                "Constructor {} tried to pass value as wrong datatype",
                constructor_name,
            );
            Ok(())
        }
        ArgsCompoundDefinition::Constructor {
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
