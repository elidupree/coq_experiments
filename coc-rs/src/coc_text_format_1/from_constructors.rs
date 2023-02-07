use crate::coc_text_format_1::{Abstraction, AbstractionKind, Command, Document, Formula};
use crate::constructors::{
    ArgsCompoundView, ArgsCompoundViewCases, ConstructorView, Constructors, TypeView,
};
use std::collections::BTreeMap;

impl AbstractionKind {
    fn of(self, parameters: impl IntoIterator<Item = (String, Formula)>, body: Formula) -> Formula {
        let mut result = body;
        let mut last = &mut result;
        for (parameter_name, parameter_type) in parameters {
            *last = Formula::Abstraction(Box::new(Abstraction {
                kind: self,
                parameter_name,
                parameter_type,
                body: std::mem::take(last),
            }));
            let Formula::Abstraction(a) = last else {unreachable!()};
            last = &mut a.body;
        }
        result
    }
}
fn apply(function: Formula, parameters: impl IntoIterator<Item = Formula>) -> Formula {
    let mut result = function;
    let last = &mut result;
    for parameter in parameters {
        *last = Formula::Apply(Box::new([std::mem::take(last), parameter]));
    }
    result
}

struct StronglyConnectedComponent<'a> {
    types: BTreeMap<&'a str, TypeView<'a>>,
}
use AbstractionKind::*;

impl StronglyConnectedComponent<'_> {
    fn return_type_name(&self, ty: TypeView) -> String {
        if self.types.len() > 1 {
            format!("R_{}", ty.name())
        } else {
            "R".to_string()
        }
    }
    fn usage_representing(&self, ty: TypeView) -> Formula {
        Formula::Usage(if self.types.contains_key(ty.name()) {
            self.return_type_name(ty)
        } else {
            ty.name().to_owned()
        })
    }
    fn type_parameters<'a>(
        &'a self,
        ty: TypeView<'a>,
    ) -> impl Iterator<Item = (String, Formula)> + 'a {
        ty.type_parameters()
            .enumerate()
            .map(move |(index, datatype)| (format!("P{index}"), self.usage_representing(datatype)))
    }
    fn constructor_parameters<'a>(
        &'a self,
        constructor: ConstructorView<'a>,
    ) -> impl Iterator<Item = (String, Formula)> + 'a {
        constructor
            .data_arguments()
            .map(move |argument| {
                (
                    argument.name().to_owned(),
                    self.usage_representing(argument.datatype()),
                )
            })
            .chain(constructor.preconditions().map(move |precondition| {
                (
                    format!("p{}", precondition.index()),
                    apply(
                        self.usage_representing(precondition.predicate_type()),
                        precondition
                            .type_parameters()
                            .map(|a| self.args_compound_formula(a)),
                    ),
                )
            }))
    }
    fn type_parameter_usages<'a>(&'a self, ty: TypeView<'a>) -> impl Iterator<Item = Formula> + 'a {
        self.type_parameters(ty).map(|(n, _)| Formula::Usage(n))
    }
    fn constructor_parameter_usages<'a>(
        &'a self,
        constructor: ConstructorView<'a>,
    ) -> impl Iterator<Item = Formula> + 'a {
        self.constructor_parameters(constructor)
            .map(|(n, _)| Formula::Usage(n))
    }
    fn return_types(&self) -> impl Iterator<Item = (String, Formula)> + '_ {
        self.types.values().map(|&ty| {
            (
                self.return_type_name(ty),
                ForAll.of(self.type_parameters(ty), Formula::Prop),
            )
        })
    }
    fn case_handler_name(&self, constructor: ConstructorView) -> String {
        format!("on_{}", constructor.name())
    }
    fn case_handler_usage(&self, constructor: ConstructorView) -> Formula {
        Formula::Usage(self.case_handler_name(constructor))
    }
    fn case_handlers(&self) -> impl Iterator<Item = (String, Formula)> + '_ {
        self.types.values().flat_map(move |&ty| {
            ty.constructors().map(move |constructor| {
                (
                    self.case_handler_name(constructor),
                    ForAll.of(
                        self.constructor_parameters(constructor),
                        apply(
                            self.usage_representing(ty),
                            self.resulting_type_parameters(constructor),
                        ),
                    ),
                )
            })
        })
    }
    fn return_types_and_case_handlers(&self) -> impl Iterator<Item = (String, Formula)> + '_ {
        self.return_types().chain(self.case_handlers())
    }
    fn args_compound_formula(&self, compound: ArgsCompoundView) -> Formula {
        match compound.cases() {
            ArgsCompoundViewCases::Argument(argument) => Formula::Usage(argument.name().to_owned()),
            ArgsCompoundViewCases::Constructor {
                constructor,
                arguments,
            } => apply(
                Formula::Usage(constructor.name().to_owned()),
                arguments.into_iter().map(|a| self.args_compound_formula(a)),
            ),
        }
    }
    fn resulting_type_parameters<'a>(
        &'a self,
        constructor: ConstructorView<'a>,
    ) -> impl Iterator<Item = Formula> + 'a {
        constructor
            .resulting_type_parameters()
            .map(move |a| self.args_compound_formula(a))
    }
    fn commands_defining_type(&self, ty: TypeView) -> Vec<Command> {
        let mut result = vec![
            Command::ClaimType(
                ty.name().to_owned(),
                ForAll.of(self.type_parameters(ty), Formula::Prop),
            ),
            Command::Assign(
                ty.name().to_owned(),
                Lambda.of(
                    self.type_parameters(ty),
                    ForAll.of(
                        self.return_types_and_case_handlers(),
                        apply(self.usage_representing(ty), self.type_parameter_usages(ty)),
                    ),
                ),
            ),
        ];
        for constructor in ty.constructors() {
            result.extend(self.commands_defining_constructor(constructor))
        }
        result
    }
    fn commands_defining_constructor(&self, constructor: ConstructorView) -> Vec<Command> {
        let ty = constructor.containing_type();
        vec![
            Command::ClaimType(
                constructor.name().to_owned(),
                ForAll.of(
                    self.type_parameters(ty)
                        .chain(self.constructor_parameters(constructor)),
                    apply(
                        Formula::Usage(ty.name().to_owned()),
                        self.resulting_type_parameters(constructor),
                    ),
                ),
            ),
            Command::Assign(
                constructor.name().to_owned(),
                Lambda.of(
                    self.type_parameters(ty)
                        .chain(self.constructor_parameters(constructor)),
                    Lambda.of(
                        self.return_types_and_case_handlers(),
                        apply(
                            self.case_handler_usage(constructor),
                            self.constructor_parameter_usages(constructor),
                        ),
                    ),
                ),
            ),
        ]
    }
}

impl Document {
    pub fn from_constructors(constructors: &Constructors) -> Self {
        //using https://en.wikipedia.org/wiki/Path-based_strong_component_algorithm
        struct StrongComponentSearch<'a> {
            constructors: &'a Constructors,
            preorder_numbers: BTreeMap<&'a str, usize>,
            component_assignments: BTreeMap<&'a str, usize>,
            components: Vec<BTreeMap<&'a str, TypeView<'a>>>,
            unassigned_stack: Vec<&'a str>,
            p_stack: Vec<&'a str>,
        }
        impl<'a> StrongComponentSearch<'a> {
            fn discover(&mut self, ty: TypeView<'a>) {
                self.preorder_numbers
                    .insert(ty.name(), self.preorder_numbers.len());
                self.unassigned_stack.push(ty.name());
                self.p_stack.push(ty.name());
                for other in ty.all_referenced_types() {
                    if let Some(other_preorder_number) = self.preorder_numbers.get(other.name()) {
                        if !self.component_assignments.contains_key(other.name()) {
                            while let Some(last) = self.p_stack.pop() {
                                if self.preorder_numbers.get(last).unwrap() <= other_preorder_number
                                {
                                    self.p_stack.push(last);
                                    break;
                                }
                            }
                        }
                    } else {
                        self.discover(other);
                    }
                }
                if self.p_stack.last() == Some(&ty.name()) {
                    let mut new_component = BTreeMap::new();
                    while let Some(last) = self.unassigned_stack.pop() {
                        new_component.insert(last, self.constructors.get(last));
                        self.component_assignments
                            .insert(last, self.components.len());
                        if last == ty.name() {
                            break;
                        }
                    }
                    self.components.push(new_component);
                    self.p_stack.pop();
                }
            }
        }
        let mut search = StrongComponentSearch {
            constructors,
            preorder_numbers: BTreeMap::new(),
            component_assignments: Default::default(),
            components: vec![],
            unassigned_stack: vec![],
            p_stack: vec![],
        };
        for ty in constructors.types() {
            if !search.preorder_numbers.contains_key(ty.name()) {
                search.discover(ty);
            }
        }
        let mut commands = Vec::new();
        for component in search.components {
            let component = StronglyConnectedComponent { types: component };
            for &ty in component.types.values() {
                commands.extend(component.commands_defining_type(ty));
            }
        }
        Document { commands }
    }
}
