#![feature(array_chunks)]
#![feature(once_cell)]

use clap::{arg, Parser};
use coc_rs::constructors::{Constructors, DataValue, Notation, NotationItem};
use coc_rs::metavariable::{CanMatch, Environment, MetavariableId};
use coc_rs::utils::{read_json_file, write_json_file};
use quick_and_dirty_web_gui::{callback, callback_with};
use std::collections::{BTreeMap, HashMap};
use std::iter::zip;
use std::sync::{LazyLock, Mutex};
use typed_html::elements::{FlowContent, PhrasingContent};
use typed_html::types::Id;
use typed_html::{elements, html, text};

pub type FlowElement = Box<dyn FlowContent<String>>;
pub type PhrasingElement = Box<dyn PhrasingContent<String>>;
pub type Span = Box<elements::span<String>>;

struct Interface {
    file_path: String,
    environment: Environment,
    focus: Option<(MetavariableId, Option<WhichChild>)>,
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum WhichChild {
    TypeParameter(usize),
    DataArgument(usize),
    Precondition(usize),
}

struct MetavariableColors {
    name_foreground: String,
    name_background: String,
    node_background: String,
    border: String,
}

impl Interface {
    fn optimized_ordering(&self) -> Vec<MetavariableId> {
        let references: HashMap<MetavariableId, Vec<MetavariableId>> = self
            .environment
            .metavariables()
            .iter()
            .map(|(&id, metavariable)| {
                (
                    id,
                    metavariable
                        .type_parameters
                        .iter()
                        .chain(metavariable.constructor.iter().flat_map(|constructor| {
                            constructor
                                .data_arguments
                                .values()
                                .chain(&constructor.preconditions)
                        }))
                        .flatten()
                        .copied()
                        .collect(),
                )
            })
            .collect();
        let mut back_references: HashMap<MetavariableId, Vec<MetavariableId>> = self
            .environment
            .metavariables()
            .iter()
            .map(|(&id, _)| (id, Vec::new()))
            .collect();
        for (&parent, children) in &references {
            for child in children {
                back_references.get_mut(child).unwrap().push(parent);
            }
        }
        let mut ordering: Vec<MetavariableId> =
            self.environment.metavariables().keys().copied().collect();
        let mut indices: HashMap<MetavariableId, usize> = ordering
            .iter()
            .enumerate()
            .map(|(index, &id)| (id, index))
            .collect();

        fn edge_loss(parent_index: usize, child_index: usize) -> f32 {
            let distance = (parent_index as f32 - child_index as f32).powi(2);
            if parent_index > child_index {
                distance
            } else {
                distance * 200.0
            }
        }

        fn all_neighbors_loss(
            index: usize,
            id: MetavariableId,
            exclude_id: Option<MetavariableId>,
            indices: &HashMap<MetavariableId, usize>,
            references: &HashMap<MetavariableId, Vec<MetavariableId>>,
            back_references: &HashMap<MetavariableId, Vec<MetavariableId>>,
        ) -> f32 {
            let mut result = 0.0;
            for &child in &references[&id] {
                if Some(child) != exclude_id {
                    result += edge_loss(index, indices[&child]);
                }
            }
            for &parent in &back_references[&id] {
                if Some(parent) != exclude_id {
                    result += edge_loss(indices[&parent], index);
                }
            }
            result
        }

        for _ in 0..10 {
            let mut changed_anything = false;
            for ix1 in 0..ordering.len() {
                for ix2 in ix1..ordering.len() {
                    let id1 = ordering[ix1];
                    let id2 = ordering[ix2];
                    let a =
                        all_neighbors_loss(ix1, id1, None, &indices, &references, &back_references);
                    let b = all_neighbors_loss(
                        ix2,
                        id2,
                        Some(id1),
                        &indices,
                        &references,
                        &back_references,
                    );

                    ordering.swap(ix1, ix2);
                    *indices.get_mut(&id1).unwrap() = ix2;
                    *indices.get_mut(&id2).unwrap() = ix1;

                    let c =
                        all_neighbors_loss(ix1, id2, None, &indices, &references, &back_references);
                    let d = all_neighbors_loss(
                        ix2,
                        id1,
                        Some(id1),
                        &indices,
                        &references,
                        &back_references,
                    );
                    if c + d < a + b {
                        changed_anything = true;
                    } else {
                        ordering.swap(ix1, ix2);
                        *indices.get_mut(&id1).unwrap() = ix1;
                        *indices.get_mut(&id2).unwrap() = ix2;
                    }
                }
            }
            if !changed_anything {
                break;
            }
        }
        ordering
    }
    fn metavariable_colors(&self, id: MetavariableId) -> MetavariableColors {
        if matches!(self.focus_slot_needed_typename(),  Some(need) if self.environment.get(id).typename != *need )
        {
            return MetavariableColors {
                name_foreground: format!("hsl(0turn 0% 40%)"),
                name_background: format!("hsl(0turn 0% 90%)"),
                node_background: format!("hsl(0turn 0% 97% / 0.8)"),
                border: format!("hsl(0turn 0% 80%)"),
            };
        }
        let bytes = id.0.as_u128().to_le_bytes();
        let [h1, h2, b, w, ..] = bytes;
        let h1 = (h1 as f64) / 255.0;
        let h2 = (h1 + 1.0 / 4.0 + ((h2 as f64) / 255.0) / 4.0).fract();
        let b = (0.6 + ((b as f64) / 255.0).powi(3) * 0.4) * 100.0;
        let w = (0.7 + ((w as f64) / 255.0).powi(2) * 0.15) * 100.0;
        let w2 = (w + 400.0) * 0.2;
        let w3 = w - 40.0;
        MetavariableColors {
            name_foreground: format!("hwb({h1}turn 0.0% {b}%)"),
            name_background: format!("hwb({h2}turn {w}% 0.0%)"),
            node_background: format!("hwb({h2}turn {w2}% 0.0% / 0.85)"),
            border: format!("hwb({h2}turn {w3}% 0.0%)"),
        }
    }
    fn implicit_name(&self, id: MetavariableId) -> String {
        let mut name = self.environment.get(id).name.clone();
        if name.is_empty() {
            let [_, _, _, _, abc @ ..] = id.0.as_u128().to_le_bytes();
            name.extend(
                abc.into_iter()
                    .take(3)
                    .map(|a| char::from_u32(((a as u32) & 63) + 63).unwrap()),
            );
        }
        name
    }
    fn inline_metavariable_reference(&self, id: MetavariableId, name: &str) -> Span {
        let MetavariableColors {
            name_foreground,
            name_background,
            ..
        } = self.metavariable_colors(id);
        let style = format!("color: {name_foreground}; background-color: {name_background}");
        let id_string = id.0.to_string();

        html! {
            <span class="metavariable_reference" style=style data-targetid=id_string/* onclick={callback(move || set_focus(id, None))}*/>
                {text!(name)}
            </span> : String
        }
    }
    fn inline_child(&self, id: Option<MetavariableId>) -> Span {
        match id {
            None => {
                html! {
                    <span class="hole invalid">
                        "_"
                    </span> : String
                }
            }
            Some(id) => self.inline_metavariable_reference(id, &self.unfolded_name(id, false)),
        }
    }
    fn unfolded_name(&self, id: MetavariableId, force_unfold: bool) -> String {
        #[derive(Debug)]
        pub enum Item {
            Text(String),
            Variable(MetavariableId),
        }
        let mut items = vec![Item::Variable(id)];
        let length = |items: &[Item]| -> usize {
            items
                .iter()
                .map(|item| match item {
                    Item::Text(text) => text.chars().count(),
                    &Item::Variable(id) => self.implicit_name(id).chars().count(),
                })
                .sum()
        };
        let mut force_unfold = force_unfold;
        let mut allow_increasing_length = true;
        loop {
            let mut next = Vec::with_capacity(items.len() * 2);
            let mut changed_anything = false;
            for item in &items {
                match item {
                    Item::Text(text) => next.push(Item::Text(text.clone())),
                    &Item::Variable(id) => {
                        let metavariable = self.environment.get(id);
                        if !metavariable.name.is_empty() && !force_unfold {
                            changed_anything = true;
                            next.push(Item::Text(metavariable.name.clone()));
                        } else if let Some(constructor) = &metavariable.constructor {
                            let type_definition = Constructors::coc()
                                .types
                                .get(&metavariable.typename)
                                .unwrap();
                            let constructor_definition =
                                type_definition.constructors.get(&constructor.name).unwrap();
                            if let Some(notation) = &constructor_definition.notation {
                                let new_items: Vec<_> = notation
                                    .items
                                    .iter()
                                    .map(|item| match item {
                                        NotationItem::Text(text) => Item::Text(text.clone()),
                                        NotationItem::Argument(argument) => {
                                            match constructor.data_arguments.get(argument).unwrap()
                                            {
                                                &Some(id) => Item::Variable(id),
                                                None => Item::Text("_".to_owned()),
                                            }
                                        }
                                    })
                                    .collect();
                                if allow_increasing_length || length(&new_items) <= 3 {
                                    changed_anything = true;
                                    next.extend(new_items);
                                } else {
                                    next.push(Item::Variable(id));
                                }
                            } else if force_unfold {
                                changed_anything = true;
                                next.push(Item::Text(format!("{} [...]", constructor.name)));
                            } else {
                                next.push(Item::Variable(id));
                            }
                        } else {
                            changed_anything = true;
                            next.push(Item::Text("_".to_owned()));
                        }
                    }
                }
            }
            if !changed_anything {
                let mut result = String::new();
                for item in items {
                    result.push_str(&match item {
                        Item::Text(text) => text,
                        Item::Variable(id) => self.implicit_name(id),
                    })
                }
                return result;
            }
            let too_long = length(&next) > 20;
            if !too_long || !allow_increasing_length {
                items = next;
            }
            if too_long {
                allow_increasing_length = false;
            }
            force_unfold = false;
        }
    }

    fn inline_data_value(
        &self,
        value: &DataValue,
        typename: &str,
        data_arguments: &BTreeMap<String, Option<MetavariableId>>,
    ) -> Span {
        let datatype = Constructors::coc().types.get(typename).unwrap();
        match value {
            DataValue::Argument(argname) => {
                self.inline_child(*data_arguments.get(argname).unwrap())
            }
            DataValue::Constructor {
                constructor,
                arguments,
            } => {
                let constructor_definition = datatype.constructors.get(constructor).unwrap();
                let arguments_map: HashMap<&String, (&DataValue, &String)> =
                    zip(&constructor_definition.data_arguments, arguments)
                        .map(|(a, v)| (&a.name, (v, &a.datatype)))
                        .collect();
                self.inline_notation(
                    constructor_definition.notation.as_ref().unwrap(),
                    |argument_name| {
                        let &(v, t) = arguments_map.get(argument_name).unwrap();
                        self.inline_data_value(v, t, data_arguments)
                    },
                )
            }
        }
    }

    fn inline_notation<T>(
        &self,
        notation: &Notation<T>,
        mut child_func: impl FnMut(&T) -> PhrasingElement,
    ) -> Span {
        let elements: Vec<PhrasingElement> = notation
            .items
            .iter()
            .map(|item| match item {
                NotationItem::Text(text) => text!(text),
                NotationItem::Argument(argument) => child_func(argument),
            })
            .collect();
        html! {
            <span class="notation">
                {elements}
            </span> : String
        }
    }

    fn focus_slot_needed_typename(&self) -> Option<&String> {
        match &self.focus {
            Some((id, Some(child))) => {
                let focus_metavariable = self.environment.get(*id);
                let focus_type_definition = Constructors::coc()
                    .types
                    .get(&focus_metavariable.typename)
                    .unwrap();
                let focus_constructor_definition = focus_metavariable
                    .constructor
                    .as_ref()
                    .map(|c| focus_type_definition.constructors.get(&c.name).unwrap());
                let needed_typename = match *child {
                    WhichChild::TypeParameter(index) => {
                        &focus_type_definition.type_parameters[index]
                    }
                    WhichChild::DataArgument(index) => {
                        &focus_constructor_definition.unwrap().data_arguments[index].datatype
                    }
                    WhichChild::Precondition(index) => {
                        &focus_constructor_definition.unwrap().preconditions[index].predicate_type
                    }
                };
                Some(needed_typename)
            }
            _ => None,
        }
    }

    fn node_element(&self, id: MetavariableId) -> FlowElement {
        let metavariable = self.environment.get(id);
        let type_definition = Constructors::coc()
            .types
            .get(&metavariable.typename)
            .unwrap();
        let validity = self.environment.local_validity(id);
        let mut lines: Vec<FlowElement> = Vec::new();
        let mut self_elements: Vec<FlowElement> = Vec::new();
        let mut child_elements: Vec<FlowElement> = Vec::new();
        let focused = matches!(self.focus, Some((i, _)) if i == id);
        let valid = validity.is_valid();

        let use_allowed = self.focus_slot_needed_typename() == Some(&metavariable.typename);

        let implicit_name = self.implicit_name(id);
        let unfolded_name = self.unfolded_name(id, true);

        let type_element = self.inline_notation(&type_definition.notation, |&index| {
            let body = self.inline_child(*metavariable.type_parameters.get(index).unwrap());
            let child_valid = *validity.type_parameters_valid.get(index).unwrap();
            let class = if matches!(self.focus, Some((i,Some(WhichChild::TypeParameter(j)))) if i==id && j==index)
            {
                "child focused"
            } else if child_valid {
                "child valid"
            } else {
                "child invalid"
            };

            html! {
                <span class=class onclick={callback(move || set_focus(id,Some (WhichChild::TypeParameter (index))))}>
                    {body}
                </span> : String
            }
        });
        if metavariable.name.is_empty()
            && metavariable.constructor.is_some()
            && unfolded_name.chars().count() <= 3
        {
            let unfolded = self.inline_metavariable_reference(id, &unfolded_name);
            lines.push(html! {
                <div>
                    {unfolded} " : "{type_element}
                </div>
            });
        } else {
            let name_id = self.inline_metavariable_reference(id, &implicit_name);
            lines.push(html! {
                <div>
                    {name_id} " : "{type_element}
                </div>
            });
            if let Some(constructor) = &metavariable.constructor {
                let constructor_definition =
                    type_definition.constructors.get(&constructor.name).unwrap();
                if let Some(notation) = &constructor_definition.notation {
                    let argument_indices: HashMap<&str, usize> = constructor_definition
                        .data_arguments
                        .iter()
                        .enumerate()
                        .map(|(index, argument)| (&*argument.name, index))
                        .collect();
                    let value_element = self.inline_notation(notation, |name| {
                        let body = self.inline_child(*constructor.data_arguments.get(name).unwrap());
                        let index = argument_indices[&**name];
                        let child_valid = *validity.data_arguments_valid.get(name).unwrap();
                        let class = if matches!(self.focus, Some((i,Some(WhichChild::DataArgument(j)))) if i==id && j==index)
                        {
                            "child focused"
                        } else if child_valid {
                            "child valid"
                        } else {
                            "child invalid"
                        };

                        html! {
                            <span class=class onclick={callback(move || set_focus(id,Some (WhichChild::DataArgument(index))))}>
                                {body}
                            </span> : String
                        }
                    });
                    lines.push(html! {
                        <div>
                            " = "{value_element}
                        </div>
                    });
                } else {
                    lines.push(html! {
                        <div>
                            " = "{text!{unfolded_name}}
                        </div>
                    });
                }
            } else {
                lines.push(html! {
                    <div>
                        " = "{self.inline_child(None)}
                    </div>
                });
            }
        }

        if focused {
            let name_element_id = format!("metavariable_{}_name", id.0);
            self_elements.push(html! {
                <input id=Id::new(&*name_element_id) type="text" value=&metavariable.name
                  oninput={callback_with(
                    &format!(r##"document.getElementById("{name_element_id}").value"##),
                    move |name: String| rename_metavariable (id,name)
                )} /> : String
            });
        }
        if focused || !valid {
            child_elements.push(html! {
                <button onclick={callback(move || autofill(id))}>
                    "Autofill"
                </button> : String
            });
        }
        match &metavariable.constructor {
            None => {
                if focused || !valid {
                    for (constructor_name, _) in type_definition.constructors.iter() {
                        let text = text!(constructor_name);
                        if self.environment.constructor_possible(id, constructor_name)
                            != CanMatch::No
                        {
                            let constructor_name = constructor_name.clone();
                            child_elements.push(html! {
                                <button onclick={callback(move || set_constructor(id,Some (constructor_name.clone())))}>
                                    {text}
                                </button> : String
                            });
                        } else {
                            child_elements.push(html! {
                                <button disabled=true>
                                    {text}
                                </button> : String
                            });
                        }
                    }
                }
            }
            Some(constructor) => {
                if focused || !valid {
                    child_elements.push(html! {
                        <button onclick={callback(move || set_constructor(id,None))}>
                            "Remove constructor"
                        </button> : String
                    });
                }
                let constructor_definition =
                    type_definition.constructors.get(&constructor.name).unwrap();
                for (index, argument_definition) in
                    constructor_definition.data_arguments.iter().enumerate()
                {
                    let body = self.inline_child(
                        *constructor
                            .data_arguments
                            .get(&argument_definition.name)
                            .unwrap(),
                    );
                    let argument_name = argument_definition.name.clone();
                    let child_valid = *validity.data_arguments_valid.get(&argument_name).unwrap();
                    let class = if matches!(self.focus, Some((i,Some(WhichChild::DataArgument(j)))) if i==id && j==index)
                    {
                        "child focused"
                    } else if child_valid {
                        "child valid"
                    } else {
                        "child invalid"
                    };

                    if focused || !valid {
                        child_elements.push(html! {
                            <div class=class onclick={callback(move || set_focus(id,Some (WhichChild::DataArgument (index))))}>
                                {text!(argument_name)} " = " {body}
                            </div> : String
                        });
                    }
                }
                for (index, (argument_definition, child_valid)) in zip(
                    &constructor_definition.preconditions,
                    validity.preconditions_valid,
                )
                .enumerate()
                {
                    let body = self.inline_child(*constructor.preconditions.get(index).unwrap());
                    let class = if matches!(self.focus, Some((i,Some(WhichChild::Precondition(j)))) if i==id && j==index)
                    {
                        "child focused"
                    } else if child_valid {
                        "child valid"
                    } else {
                        "child invalid"
                    };

                    let predicate_definition = Constructors::coc()
                        .types
                        .get(&argument_definition.predicate_type)
                        .unwrap();

                    let full_type = self.inline_notation(&predicate_definition.notation, |&index| {
                        let value = argument_definition.type_parameters.get(index).unwrap();
                        let typename = predicate_definition
                            .type_parameters
                            .get(index)
                            .unwrap();
                        let body = self.inline_data_value(value, typename, &constructor.data_arguments);
                        let valid = true; //*validity.type_parameters_valid.get(index).unwrap();
                        let class = if valid {
                            "child valid"
                        } else {
                            "child invalid"
                        };

                        html! {
                            <span class=class onclick={callback(move || set_focus(id,Some (WhichChild::TypeParameter (index))))}>
                                {body}
                            </span> : String
                        }
                    });

                    child_elements.push(html! {
                        <div class=class onclick={callback(move || set_focus(id,Some (WhichChild::Precondition (index))))}>
                            {body}" : "{full_type}  
                        </div> : String
                    });
                }

                if focused || !valid {
                    child_elements.push(text!("->"));
                    child_elements.push(self.inline_notation(
                        &type_definition.notation,
                        |&index: &usize| {
                            let typename = type_definition.type_parameters.get(index).unwrap();
                            let value = constructor_definition
                                .resulting_type_parameters
                                .get(index)
                                .unwrap();
                            let valid = *validity.return_type_parameters_valid.get(index).unwrap();

                            let class = if valid {
                                "child valid"
                            } else {
                                "child invalid"
                            };

                            html! {
                                <span class=class>
                                    {self.inline_data_value(value,typename,&constructor.data_arguments)}
                                </span> : String
                            }
                        },
                    ));
                }
            }
        }
        let MetavariableColors {
            node_background,
            border,
            ..
        } = self.metavariable_colors(id);
        let style = format!("background-color: {node_background}; border-color: {border};");
        let onclick = callback(move || {
            if use_allowed {
                use_metavariable(id)
            } else {
                set_focus(id, None)
            }
        });
        // why make a binding for this? just to suppress an IDE bug
        // Note: This exact ID is referenced in the js
        let result: FlowElement = html! {
            <div class="node" style=style data-color=border id=Id::new(&*format!("metavariable_{}", id.0)) onclick=onclick>
                {lines}
                <div class="name_etc">
                    {self_elements}
                </div>
                <div class="arguments">
                    {child_elements}
                </div>
            </div> : String
        };
        result
    }
    fn nodes(&self) -> FlowElement {
        // let nodes = self
        //     .environment
        //     .metavariables()
        //     .iter()
        //     .map(|(&id, _)| self.node_element(id));
        let nodes = self
            .optimized_ordering()
            .into_iter()
            .map(|id| self.node_element(id));
        let new = if let Some((_id, Some(_child))) = &self.focus {
            let style = format!(
                "background-color: hsl(0turn 100% 97% / 0.8); border-color: hsl(0turn 100% 80%);"
            );
            Some(html! {
                <div class="node" style=style onclick={callback(move || new_child())}>
                    "(Create...)"
                </div> : String
            })
        } else {
            None
        };
        html! {
            <div class="nodes" onclick={callback(move || unfocus())}>
                {nodes}
                {new}
            </div> : String
        }
    }
    fn whole_page(&self) -> FlowElement {
        let nodes = self.nodes();
        let new_buttons = Constructors::coc().types.keys().cloned().map(|typename| {
            let text = text!(&typename);
            html! {
                <div class="new_metavariable">
                    <button onclick={callback(move || new_global(typename.clone()))}>
                        {text}
                    </button>
                </div> : String
            }
        });
        html! {
            <div class="page">
                <div class="new_metavariables">
                    {new_buttons}
                </div>
                {nodes}
                <div style="clear: both"></div>
            </div>
        }
    }

    fn update_gui(&self) {
        quick_and_dirty_web_gui::replace_html(self.whole_page().to_string());
    }

    fn set_focus(&mut self, id: MetavariableId, child: Option<WhichChild>) {
        if child.is_none() {
            let metavariable = self.environment.get(id);
            for (index, parameter) in metavariable.type_parameters.iter().enumerate() {
                if parameter.is_none() {
                    self.focus = Some((id, Some(WhichChild::TypeParameter(index))));
                    return;
                }
            }
            if let Some(constructor) = &metavariable.constructor {
                let constructor_definition = Constructors::coc()
                    .types
                    .get(&metavariable.typename)
                    .unwrap()
                    .constructors
                    .get(&constructor.name)
                    .unwrap();
                for (index, argument) in constructor_definition.data_arguments.iter().enumerate() {
                    if constructor
                        .data_arguments
                        .get(&argument.name)
                        .unwrap()
                        .is_none()
                    {
                        self.focus = Some((id, Some(WhichChild::DataArgument(index))));
                        return;
                    }
                }
                for (index, argument) in constructor.preconditions.iter().enumerate() {
                    if argument.is_none() {
                        self.focus = Some((id, Some(WhichChild::Precondition(index))));
                        return;
                    }
                }
            }
        }
        self.focus = Some((id, child));
    }

    fn new_child(&mut self) {
        let Some((id, Some(which_child))) = self.focus.take() else { return };

        let metavariable = self.environment.get(id);
        let type_definition = Constructors::coc()
            .types
            .get(&metavariable.typename)
            .unwrap();

        match which_child {
            WhichChild::TypeParameter(index) => {
                let new_id = self
                    .environment
                    .create_metavariable(type_definition.type_parameters[index].clone());
                self.environment.set_type_parameter(id, index, Some(new_id));
                self.set_focus(new_id, None);
            }
            WhichChild::DataArgument(index) => {
                let Some(constructor) = &metavariable.constructor else { return };
                let constructor_definition =
                    type_definition.constructors.get(&constructor.name).unwrap();
                let new_id = self.environment.create_metavariable(
                    constructor_definition.data_arguments[index]
                        .datatype
                        .clone(),
                );
                self.environment.set_data_argument(
                    id,
                    &constructor_definition.data_arguments[index].name,
                    Some(new_id),
                );
                self.set_focus(new_id, None);
            }
            WhichChild::Precondition(index) => {
                let Some(constructor) = &metavariable.constructor else { return };
                let constructor_definition =
                    type_definition.constructors.get(&constructor.name).unwrap();
                let new_id = self.environment.create_metavariable(
                    constructor_definition.preconditions[index]
                        .predicate_type
                        .clone(),
                );
                self.environment.set_precondition(id, index, Some(new_id));
                // for (tpi, &type_parameter) in something.type_parameters.iter().enumerate() {
                //     self.environment
                //         .set_type_parameter(new_id, tpi, type_parameter????);
                // }

                self.set_focus(new_id, None);
            }
        }
    }
}

static INTERFACE: LazyLock<Mutex<Interface>> = LazyLock::new(|| {
    let args = Args::parse();
    let environment = read_json_file::<_, Environment>(&args.file_path)
        .unwrap_or_else(|_| Environment::default());
    Mutex::new(Interface {
        file_path: args.file_path,
        environment,
        focus: None,
    })
});

fn with_interface(f: impl FnOnce(&mut Interface)) {
    let mut interface = INTERFACE.lock().unwrap();
    f(&mut *interface);
    //interface.optimize_positions();
    interface.update_gui();
    write_json_file(&interface.file_path, &interface.environment).unwrap();
}

fn unfocus() {
    with_interface(|interface: &mut Interface| {
        interface.focus = None;
    });
}

fn new_child() {
    with_interface(Interface::new_child);
}

fn set_focus(id: MetavariableId, child: Option<WhichChild>) {
    with_interface(|interface: &mut Interface| {
        interface.set_focus(id, child);
    });
}

fn autofill(id: MetavariableId) {
    with_interface(|interface: &mut Interface| {
        interface.environment.autofill(id);
    });
}

fn set_constructor(id: MetavariableId, constructor: Option<String>) {
    with_interface(|interface: &mut Interface| {
        interface.environment.set_constructor(id, constructor);
        interface.set_focus(id, None);
    });
}

fn use_metavariable(id: MetavariableId) {
    with_interface(|interface: &mut Interface| {
        if let Some((focus_id, Some(focused_child))) = interface.focus {
            match focused_child {
                WhichChild::TypeParameter(index) => {
                    interface
                        .environment
                        .set_type_parameter(focus_id, index, Some(id));
                }
                WhichChild::DataArgument(index) => {
                    let focus = interface.environment.get(focus_id);
                    // TODO this should be 1 line of code or less
                    let name = &Constructors::coc()
                        .types
                        .get(&focus.typename)
                        .unwrap()
                        .constructors
                        .get(&focus.constructor.as_ref().unwrap().name)
                        .unwrap()
                        .data_arguments[index]
                        .name;
                    interface
                        .environment
                        .set_data_argument(focus_id, name, Some(id));
                }
                WhichChild::Precondition(index) => {
                    interface
                        .environment
                        .set_precondition(focus_id, index, Some(id));
                }
            }
            interface.set_focus(focus_id, None);
        }
    });
}

fn rename_metavariable(id: MetavariableId, name: String) {
    with_interface(|interface: &mut Interface| {
        interface.environment.rename(id, name);
    });
}

fn new_global(typename: String) {
    with_interface(|interface: &mut Interface| {
        let id = interface.environment.create_metavariable(typename);
        interface.set_focus(id, None);
    });
}

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to data file
    #[arg(short, long)]
    file_path: String,
}

#[actix_web::main]
async fn main() {
    with_interface(|_| {});
    // actix_web::rt::spawn(async {
    //     loop {
    //         actix_web::rt::time::sleep(Duration::from_millis(1000)).await;
    //         with_interface(|_| {});
    //     }
    // });
    quick_and_dirty_web_gui::launch(4986).await;
}
