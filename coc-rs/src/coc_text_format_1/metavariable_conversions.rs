use crate::coc_text_format_1::AbstractionKind::{ForAll, Lambda};
use crate::coc_text_format_1::{AbstractionKind, Command, Formula};
use crate::metavariable::{Environment, MetavariableId};
use arrayvec::ArrayVec;
use serde::{Deserialize, Serialize};
use siphasher::sip128::{Hasher128, SipHasher};
use std::collections::HashMap;
use std::hash::Hash;

pub struct MetavariablesInjectionContext<'a> {
    environment: &'a mut Environment,
    injected_formulas_by_name: HashMap<String, MetavariableId>,
    ids_by_complete_structure: HashMap<StructuralId, Vec<MetavariableId>>,
    ids_by_type_structure: HashMap<StructuralId, Vec<MetavariableId>>,
    ids_by_abstraction_kind: HashMap<AbstractionKind, MetavariableId>,
    structures_by_id: HashMap<MetavariableId, StructuralId>,
}

#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Default, Debug,
)]
struct StructuralId(u128);

#[derive(Hash, Default)]
struct StructuralIdMaker {
    name: String,
    typename: String,
    type_parameters: Vec<StructuralId>,
    constructor: String,
    data_arguments: Vec<StructuralId>,
    preconditions: Vec<StructuralId>,
}

impl StructuralIdMaker {
    fn abstraction_kind(kind: AbstractionKind) -> Self {
        StructuralIdMaker {
            typename: "AbstractionKind".to_string(),
            constructor: format!("{:?}", kind),
            ..Default::default()
        }
    }
    fn make_id(&self) -> StructuralId {
        let mut hasher = SipHasher::new_with_keys(0x09b1a3338349fa34, 0x24aa9b72e6020897);
        self.hash(&mut hasher);
        StructuralId(hasher.finish128().as_u128())
    }
}

#[derive(Debug)]
struct InjectFormulaResult {
    id: MetavariableId,
    binding_trees_by_free_variable: HashMap<String, MetavariableId>,
}

impl Formula {
    fn constructor_name(&self) -> Option<&'static str> {
        Some(match self {
            Formula::Prop => "Prop",
            Formula::Usage(_) => "Usage",
            Formula::Hole => return None,
            Formula::Abstraction(_) => "Abstraction",
            Formula::Apply(_) => "Apply",
        })
    }
}

enum BindingTree {
    Hole,
    BindNotThis,
    BindVariable,
    BindBranch([MetavariableId; 2]),
}

impl BindingTree {
    fn constructor_name(&self) -> Option<&'static str> {
        Some(match self {
            BindingTree::Hole => return None,
            BindingTree::BindNotThis => "BindNotThis",
            BindingTree::BindVariable => "BindVariable",
            BindingTree::BindBranch(_) => "BindBranch",
        })
    }
}

impl MetavariablesInjectionContext<'_> {
    pub fn for_environment(environment: &mut Environment) -> MetavariablesInjectionContext {
        let mut result = MetavariablesInjectionContext {
            environment,
            injected_formulas_by_name: Default::default(),
            ids_by_complete_structure: Default::default(),
            ids_by_type_structure: Default::default(),
            ids_by_abstraction_kind: Default::default(),
            structures_by_id: Default::default(),
        };
        result.init();
        result
    }
    fn init(&mut self) {
        // use something like Kahn's algorithm to assemble all the structures of existing nodes
        let mut parents: HashMap<MetavariableId, Vec<MetavariableId>> = HashMap::new();
        let mut type_parents: HashMap<MetavariableId, Vec<MetavariableId>> = HashMap::new();
        let mut num_type_parameters_not_known_complete: HashMap<MetavariableId, usize> =
            HashMap::new();
        let mut num_children_not_known_complete: HashMap<MetavariableId, usize> = HashMap::new();
        let mut complete_structure_stack = Vec::new();
        let mut complete_type_structure_stack = Vec::new();
        for metavariable in self.environment.metavariables() {
            if let Some(children) = metavariable
                .type_parameters()
                .map(|c| c.child().map(|c| c.id()))
                .collect::<Option<Vec<MetavariableId>>>()
            {
                if children.is_empty() {
                    complete_type_structure_stack.push(metavariable.id());
                }
                num_type_parameters_not_known_complete.insert(metavariable.id(), children.len());
                for child in children {
                    type_parents
                        .entry(child)
                        .or_default()
                        .push(metavariable.id());
                }
            }
            if metavariable.constructor().is_some() {
                if let Some(children) = metavariable
                    .all_children()
                    .map(|c| c.map(|c| c.id()))
                    .collect::<Option<Vec<MetavariableId>>>()
                {
                    if children.is_empty() {
                        complete_structure_stack.push(metavariable.id());
                    }
                    num_children_not_known_complete.insert(metavariable.id(), children.len());
                    for child in children {
                        parents.entry(child).or_default().push(metavariable.id());
                    }
                }
            }
        }
        while let Some(id) = complete_structure_stack.pop() {
            let metavariable = self.environment.get(id).unwrap();
            let constructor = metavariable.constructor().unwrap();
            let id_maker = StructuralIdMaker {
                name: metavariable.name().to_string(),
                typename: metavariable.typename().to_string(),
                type_parameters: metavariable
                    .type_parameters()
                    .map(|c| self.structures_by_id[&c.child().unwrap().id()])
                    .collect(),
                constructor: constructor.name().to_string(),
                data_arguments: constructor
                    .data_arguments()
                    .map(|c| self.structures_by_id[&c.child().unwrap().id()])
                    .collect(),
                preconditions: constructor
                    .preconditions()
                    .map(|c| self.structures_by_id[&c.child().unwrap().id()])
                    .collect(),
            };
            let structural_id = id_maker.make_id();
            self.structures_by_id.insert(id, structural_id);
            self.ids_by_complete_structure
                .entry(structural_id)
                .or_default()
                .push(id);
            for &parent in parents.get(&id).into_iter().flatten() {
                let count = num_children_not_known_complete.get_mut(&parent).unwrap();
                *count -= 1;
                if *count == 0 {
                    complete_structure_stack.push(parent)
                }
            }
            for &parent in type_parents.get(&id).into_iter().flatten() {
                let count = num_type_parameters_not_known_complete
                    .get_mut(&parent)
                    .unwrap();
                *count -= 1;
                if *count == 0 {
                    complete_type_structure_stack.push(parent)
                }
            }
        }
        for id in complete_type_structure_stack {
            let metavariable = self.environment.get(id).unwrap();

            let id_maker = StructuralIdMaker {
                name: metavariable.name().to_string(),
                typename: metavariable.typename().to_string(),
                type_parameters: metavariable
                    .type_parameters()
                    .map(|c| self.structures_by_id[&c.child().unwrap().id()])
                    .collect(),
                ..Default::default()
            };
            let structural_id = id_maker.make_id();
            self.ids_by_type_structure
                .entry(structural_id)
                .or_default()
                .push(id);
        }

        for kind in [Lambda, ForAll] {
            let structural_id = StructuralIdMaker::abstraction_kind(kind).make_id();
            let ids = self
                .ids_by_complete_structure
                .entry(structural_id)
                .or_insert_with(|| {
                    let id = self
                        .environment
                        .create_metavariable("AbstractionKind".to_owned());
                    self.environment
                        .set_constructor(id, Some(format!("{:?}", kind)));
                    vec![id]
                });
            self.ids_by_abstraction_kind.insert(kind, ids[0]);
        }
    }
    fn formula_child_ids(
        &self,
        formula: &Formula,
        child_results: &[InjectFormulaResult],
    ) -> ArrayVec<MetavariableId, 4> {
        let mut result = ArrayVec::new();
        match formula {
            Formula::Abstraction(a) => {
                let binding_tree_id = child_results[1]
                    .binding_trees_by_free_variable
                    .get(&a.parameter_name)
                    .copied()
                    .unwrap_or_else(|| child_results[1].binding_trees_by_free_variable["_"]);
                result.push(self.ids_by_abstraction_kind[&a.kind]);
                result.push(child_results[0].id);
                result.push(child_results[1].id);
                result.push(binding_tree_id);
            }
            Formula::Apply(_) => {
                result.push(child_results[0].id);
                result.push(child_results[1].id);
            }
            _ => {}
        }
        result
    }
    fn binding_tree_structural_id(
        &self,
        tree: &BindingTree,
        name: Option<&str>,
    ) -> Option<StructuralId> {
        let mut id_maker = StructuralIdMaker {
            typename: "BindingTree".to_owned(),
            constructor: tree.constructor_name()?.to_owned(),
            ..Default::default()
        };
        if let Some(name) = name {
            id_maker.name = name.to_owned();
        }
        if let BindingTree::BindBranch(child_ids) = tree {
            for id in child_ids {
                id_maker
                    .data_arguments
                    .push(*self.structures_by_id.get(id)?);
            }
        }
        Some(id_maker.make_id())
    }
    fn formula_structural_id(
        &self,
        formula: &Formula,
        name: Option<&str>,
        child_results: &[InjectFormulaResult],
    ) -> Option<StructuralId> {
        let mut id_maker = StructuralIdMaker {
            typename: "Formula".to_owned(),
            constructor: formula.constructor_name()?.to_owned(),
            ..Default::default()
        };
        if let Some(name) = name {
            id_maker.name = name.to_owned();
        }
        // if let Formula::Usage(uname) = formula {
        //     assert!(
        //         name.is_none(),
        //         "You can't have explicit aliases right now for technical reasons"
        //     );
        //     id_maker.name = uname.to_owned();
        // }
        for id in self.formula_child_ids(formula, child_results) {
            id_maker
                .data_arguments
                .push(*self.structures_by_id.get(&id)?);
        }
        Some(id_maker.make_id())
    }
    fn inject_binding_tree(&mut self, tree: &BindingTree, name: Option<&str>) -> MetavariableId {
        let structural_id = self.binding_tree_structural_id(tree, name);
        let preexisting = structural_id.and_then(|structural_id| {
            self.ids_by_complete_structure
                .get(&structural_id)
                .and_then(|a| a.first())
                .copied()
        });
        preexisting.unwrap_or_else(|| {
            let id = self
                .environment
                .create_metavariable("BindingTree".to_string());
            self.environment
                .set_constructor(id, tree.constructor_name().map(ToOwned::to_owned));
            if let BindingTree::BindBranch(child_ids) = tree {
                for (index, &child_id) in child_ids.iter().enumerate() {
                    self.environment
                        .set_data_argument_indexed(id, index, Some(child_id));
                }
            }
            if let Some(structural_id) = structural_id {
                self.ids_by_complete_structure
                    .entry(structural_id)
                    .or_default()
                    .push(id);
            }
            id
        })
    }
    fn inject_formula(&mut self, formula: &Formula, name: Option<&str>) -> InjectFormulaResult {
        let mut child_results: ArrayVec<InjectFormulaResult, 2> = ArrayVec::new();
        match formula {
            Formula::Abstraction(a) => {
                child_results.push(self.inject_formula(&a.parameter_type, None));
                child_results.push(self.inject_formula(&a.body, None));
            }
            Formula::Apply(children) => {
                child_results.extend(children.iter().map(|c| self.inject_formula(c, None)))
            }
            _ => {}
        }
        let structural_id = self.formula_structural_id(formula, name, &child_results);
        let preexisting = structural_id.and_then(|structural_id| {
            self.ids_by_complete_structure
                .get(&structural_id)
                .and_then(|a| a.first())
                .copied()
        });
        let id = preexisting.unwrap_or_else(|| {
            let id = self.environment.create_metavariable("Formula".to_string());
            if let Some(name) = name {
                self.environment.rename(id, name.to_owned());
            }
            self.environment
                .set_constructor(id, formula.constructor_name().map(ToOwned::to_owned));
            for (index, &child_id) in self
                .formula_child_ids(formula, &child_results)
                .iter()
                .enumerate()
            {
                self.environment
                    .set_data_argument_indexed(id, index, Some(child_id));
            }
            if let Some(structural_id) = structural_id {
                self.ids_by_complete_structure
                    .entry(structural_id)
                    .or_default()
                    .push(id);
            }
            id
        });
        if let Some(name) = name {
            self.injected_formulas_by_name.insert(name.to_owned(), id);
        }

        let mut binding_trees_by_free_variable = HashMap::new();
        if let [left, right] = child_results.as_slice() {
            let left_trees = &left.binding_trees_by_free_variable;
            let mut right_trees = right.binding_trees_by_free_variable.clone();
            if let Formula::Abstraction(a) = formula {
                if a.parameter_name != "_" {
                    right_trees.remove(&a.parameter_name);
                }
            }
            for (name, &left_tree) in left_trees {
                let right_tree = right_trees
                    .get(name)
                    .copied()
                    .unwrap_or_else(|| right_trees["_"]);
                binding_trees_by_free_variable.insert(
                    name.clone(),
                    self.inject_binding_tree(
                        &BindingTree::BindBranch([left_tree, right_tree]),
                        None,
                    ),
                );
            }
            for (name, right_tree) in right_trees {
                if !left_trees.contains_key(&name) {
                    let left_tree = left_trees["_"];
                    binding_trees_by_free_variable.insert(
                        name,
                        self.inject_binding_tree(
                            &BindingTree::BindBranch([left_tree, right_tree]),
                            None,
                        ),
                    );
                }
            }
        }

        match formula {
            Formula::Prop => {
                binding_trees_by_free_variable.insert(
                    "_".to_string(),
                    self.inject_binding_tree(&BindingTree::BindNotThis, None),
                );
            }
            Formula::Usage(n) => {
                binding_trees_by_free_variable.insert(
                    n.to_string(),
                    self.inject_binding_tree(&BindingTree::BindVariable, None),
                );
                binding_trees_by_free_variable.insert(
                    "_".to_string(),
                    self.inject_binding_tree(&BindingTree::BindNotThis, None),
                );
            }
            Formula::Hole => {
                binding_trees_by_free_variable.insert(
                    "_".to_string(),
                    self.inject_binding_tree(&BindingTree::Hole, None),
                );
            }
            _ => {}
        }
        InjectFormulaResult {
            id,
            binding_trees_by_free_variable,
        }
    }
    pub fn inject_commands(&mut self, commands: &[Command]) {
        for command in commands {
            if let Command::Assign(name, formula) = command {
                self.inject_formula(formula, Some(name));
            }
        }
        for command in commands {
            if let Command::ClaimType(name, formula) = command {
                let type_result = self.inject_formula(formula, None);
                let Some(&value_id) = self.injected_formulas_by_name.get(name) else {
                    panic!("Tried to claim type of formula with name {name}, but it didn't exist");
                };
                let mut preexisting = None;
                if let (Some(&vs), Some(&ts)) = (
                    self.structures_by_id.get(&value_id),
                    self.structures_by_id.get(&type_result.id),
                ) {
                    let id_maker = StructuralIdMaker {
                        typename: "HasType".to_string(),
                        type_parameters: vec![vs, ts],
                        ..Default::default()
                    };
                    preexisting = self
                        .ids_by_type_structure
                        .get(&id_maker.make_id())
                        .and_then(|v| v.first())
                        .copied();
                }
                if preexisting.is_none() {
                    let type_proposition =
                        self.environment.create_metavariable("HasType".to_owned());
                    self.environment
                        .set_type_parameter(type_proposition, 0, Some(value_id));
                    self.environment
                        .set_type_parameter(type_proposition, 1, Some(type_result.id));
                }
            }
        }
    }
}

// impl Command {
//     pub fn inject_as_metavariables(environment: &mut Environment) {
//         let mut existing_names: HashMap<String, Vec<MetavariableId>> = HashMap::new();
//         for metavariable in environment.metavariables() {
//             existing_names
//                 .entry(metavariable.name().to_owned())
//                 .or_default()
//                 .push(metavariable.id());
//         }
//     }
// }
