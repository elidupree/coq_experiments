#![feature(array_chunks)]
#![feature(once_cell)]
#![feature(default_free_fn)]

use arrayvec::ArrayVec;
use clap::Parser;
use coc_rs::term::RecursiveTermKind;
use coc_rs::term_variable::{
    ElementaryDisproofsOfElementaryJudgments, Environment, Sort, TermContents, TermValue,
    TermVariableId,
};
use coc_rs::utils::{read_json_file, write_json_file};
use quick_and_dirty_web_gui::{callback, callback_with};
use std::default::default;
use std::sync::{LazyLock, Mutex};
use typed_html::elements::{FlowContent, PhrasingContent};
use typed_html::types::Id;
use typed_html::{elements, html, text};

pub type FlowElement = Box<dyn FlowContent<String>>;
pub type PhrasingElement = Box<dyn PhrasingContent<String>>;
pub type Span = Box<elements::span<String>>;

struct Interface {
    file_path: String,
    terms: Environment,
    focus: TermVariableId,
    clipboard: TermVariableId,
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum WhichChild {
    Lhs,
    Rhs,
}

type InvalidPaths = ArrayVec<ArrayVec<WhichChild, 2>, 3>;

fn sub_paths(paths: &InvalidPaths, child: WhichChild) -> InvalidPaths {
    paths
        .iter()
        .filter_map(|path| {
            (path.first() == Some(&child)).then(|| path.iter().copied().skip(1).collect())
        })
        .collect()
}

impl Interface {
    fn inline_term_name_id(&self, id: TermVariableId) -> Span {
        let name = &self.terms.get_term(id).name;
        let bytes = id.0.as_u128().to_le_bytes();
        let [h1, h2, b, w, abc @ ..] = bytes;
        let h1 = (h1 as f64) / 255.0;
        let h2 = (h1 + 1.0 / 4.0 + ((h2 as f64) / 255.0) / 4.0).fract();
        let b = (0.6 + ((b as f64) / 255.0).powi(3) * 0.4) * 100.0;
        let w = (0.7 + ((w as f64) / 255.0).powi(2) * 0.15) * 100.0;

        let mut name = name.to_string();
        if name.is_empty() {
            name.extend(
                abc.into_iter()
                    .take(3)
                    .map(|a| char::from_u32(((a as u32) & 63) + 63).unwrap()),
            );
        }
        let style =
            format!("color: hwb({h1}turn 0.0% {b}%); background-color: hwb({h2}turn {w}% 0.0%)");

        html! {
            <span class="term_name_id" style=style onclick={callback(move || focus_term(id))}>
                {text!(name)}
            </span> : String
        }
    }
    fn inline_term(&self, id: TermVariableId, depth_limit: usize) -> Span {
        self.inline_term_with_invalid_paths(id, depth_limit, default())
    }
    fn inline_term_with_invalid_paths_body(
        &self,
        id: TermVariableId,
        depth_limit: usize,
        invalid_paths: InvalidPaths,
    ) -> Span {
        if let TermContents::Reference(target) = self.terms.get_term(id).contents {
            if !self.terms.is_sort(target) {
                return self.inline_term_name_id(target);
            }
        }

        let Some(value) = self.terms.get_value(id) else {
            return html! {
                    <span class="hole">
                        "_"
                    </span>
                };
        };

        match *value {
            TermValue::VariableUsage(v) => {
                html! {
                    <span class="variable-usage">
                        "$"
                        {self.inline_term_name_id(v)}
                    </span>
                }
            }
            TermValue::Sort(sort) => {
                let name = match sort {
                    Sort::Prop => "ℙ",
                    Sort::Type => "𝕋",
                };
                html! {
                    <span class="sort">
                        {text!(name)}
                    </span>
                }
            }
            TermValue::Recursive {
                kind,
                child_ids,
                type_id: _,
            } => {
                if depth_limit == 0 {
                    self.inline_term_name_id(id)
                } else {
                    use RecursiveTermKind::*;
                    match kind {
                        Lambda | ForAll => {
                            let sigil = match kind {
                                Lambda => "λ",
                                ForAll => "∀",
                                _ => unreachable!(),
                            };
                            let var = self.inline_term_name_id(child_ids[0]);
                            let var_ty = (depth_limit > 1).then(|| {
                                html! {
                                        <span class="type">
                                            {self.inline_term_with_invalid_paths(child_ids[0], 1, sub_paths(&invalid_paths, WhichChild::Lhs))}
                                        </span>
                                    }
                            });
                            let body = self.inline_term_with_invalid_paths(
                                child_ids[1],
                                depth_limit - 1,
                                sub_paths(&invalid_paths, WhichChild::Rhs),
                            );
                            html! {
                                <span class="abstraction">
                                    {text!(sigil)}
                                    "("{var}{var_ty}"), "
                                    {body}
                                </span>
                            }
                        }
                        Apply => {
                            let f = self.inline_term_with_invalid_paths(
                                child_ids[0],
                                depth_limit - 1,
                                sub_paths(&invalid_paths, WhichChild::Lhs),
                            );
                            let arg = self.inline_term_with_invalid_paths(
                                child_ids[1],
                                1,
                                sub_paths(&invalid_paths, WhichChild::Rhs),
                            );
                            html! {
                                <span class="application">
                                    "("{f}" "{arg}")"
                                </span>
                            }
                        }
                    }
                }
            }
        }
    }
    fn inline_term_with_invalid_paths(
        &self,
        id: TermVariableId,
        depth_limit: usize,
        invalid_paths: InvalidPaths,
    ) -> Span {
        let body: Span =
            self.inline_term_with_invalid_paths_body(id, depth_limit, invalid_paths.clone());
        let class = if invalid_paths.contains(&ArrayVec::new()) {
            "invalid"
        } else {
            ""
        };
        html! {
            <span class=class onclick={callback(move || focus_term(id))}>
                {body}
            </span> : String
        }
    }
    fn copy_buttons(&self, id: TermVariableId) -> FlowElement {
        html! {
            <div class="buttons">
                <button onclick={callback(move || copy_term(id))}>
                    "Copy"
                </button>
                <button onclick={callback(move || use_term(id))}>
                    "UseRef"
                </button>
                <button onclick={callback(move || use_var(id))}>
                    "UseVar"
                </button>
            </div> : String
        }
    }
    fn context_element(&self, id: TermVariableId) -> FlowElement {
        html! {
            <div class="context_element" onclick={callback(move || focus_term(id))}>
                {self.inline_term_name_id(id)}
                <span class="type">
                    {self.inline_term(id, 3)}
                </span>
                <button onclick={callback(move || use_var(id))}>
                    "UseVar"
                </button>
            </div> : String
        }
    }
    fn context(&self, id: TermVariableId) -> FlowElement {
        let elements = self.terms.context(id).map(|i| self.context_element(i));
        html! {
            <div class="context">
                {elements}
            </div> : String
        }
    }

    fn global(&self, id: TermVariableId) -> FlowElement {
        let validity = self.terms.local_validity(id);
        let class = if validity.is_invalid() {
            "global invalid"
        } else {
            "global"
        };
        let mut type_invalid = false;
        let mut invalid_paths: InvalidPaths = ArrayVec::new();
        match validity {
            ElementaryDisproofsOfElementaryJudgments::TriviallyConsistent => {}
            ElementaryDisproofsOfElementaryJudgments::ForAll {
                argument_type_type_is_not_sort,
                type_is_not_sort,
                return_type_type_is_not_sort,
                type_not_known_to_be_definitionally_equal_to_return_type_type,
            } => {
                type_invalid = type_is_not_sort
                    || type_not_known_to_be_definitionally_equal_to_return_type_type;
                if argument_type_type_is_not_sort {
                    invalid_paths.push([WhichChild::Lhs].into_iter().collect());
                }
                if return_type_type_is_not_sort
                    || type_not_known_to_be_definitionally_equal_to_return_type_type
                {
                    invalid_paths.push([WhichChild::Rhs].into_iter().collect());
                }
            }
            ElementaryDisproofsOfElementaryJudgments::Lambda {
                argument_type_type_is_not_sort,
                type_is_not_forall,
                argument_type_not_known_to_be_definitionally_equal_to_type_argument_type,
                body_type_not_known_to_be_definitionally_equal_to_type_return_type,
            } => {
                type_invalid = type_is_not_forall;
                if argument_type_type_is_not_sort
                    || argument_type_not_known_to_be_definitionally_equal_to_type_argument_type
                {
                    invalid_paths.push([WhichChild::Lhs].into_iter().collect());
                }
                if body_type_not_known_to_be_definitionally_equal_to_type_return_type {
                    invalid_paths.push([WhichChild::Rhs].into_iter().collect());
                }
            }
            ElementaryDisproofsOfElementaryJudgments::Apply { .. } => {}
        }
        let ty = self.terms.get_type_id(id).map(|type_id| {
            let ty_class = if type_invalid { "type invalid" } else { "type" };
            html! {
                <span class=ty_class>
                    {self.inline_term(type_id, 3)}
                </span>
            }
        });
        html! {
            <div class=class onclick={callback(move || focus_term(id))}>
                <div class="spec">
                    {self.inline_term_name_id(id)}
                    <span class="value">
                        {self.inline_term_with_invalid_paths(id, 3, invalid_paths)}
                    </span>
                    {ty}
                </div>
                {self.copy_buttons(id)}
            </div> : String
        }
    }
    fn globals(&self) -> FlowElement {
        let mut named_globals = Vec::new();
        let mut goals = Vec::new();
        let mut other_terms = Vec::new();
        for (&id, term) in self.terms.term_variables() {
            if term.name != "" && term.parent.is_none() {
                named_globals.push((id, term));
            } else if self.terms.local_validity(id).is_invalid() {
                goals.push((id, term));
            } else if term.parent.is_none() {
                other_terms.push((id, term));
            }
        }
        named_globals.sort_by_key(|&(id, term)| (term.name.clone(), id));
        other_terms.sort_by_key(|&(id, _term)| id);
        let individual_globals = named_globals
            .into_iter()
            .chain(other_terms)
            .chain(goals)
            .map(|(id, _term)| self.global(id));
        html! {
            <div class="globals">
                {individual_globals}
                // <div class="new_global">
                //     <input id="new_global_name" type="text"/>
                //     <button onclick={callback_with(r##"$("#new_global_name").value"##, new_global)}>
                //         "Create"
                //     </button>
                // </div>
                <div class="new_global">
                    <button onclick={callback(new_global)}>
                        "New global"
                    </button>
                </div>
            </div> : String
        }
    }

    fn node_element(&self, id: TermVariableId, focused: bool, _depth: usize) -> FlowElement {
        let term = self.terms.get_term(id);
        let mut self_elements: Vec<FlowElement> = Vec::new();
        let mut context_elements: Vec<FlowElement> = Vec::new();
        let mut button_elements: Vec<FlowElement> = Vec::new();
        let name_element_id = format!("term_{}_name", id.0);
        if focused {
            context_elements.push(self.context(id));
        }
        self_elements.push(html! {
            <input id=Id::new(&*name_element_id) type="text" value=&term.name
              oninput={callback_with(
                &format!(r##"document.getElementById("{name_element_id}").value"##),
                move |name: String| rename_term (id,name)
            )} /> : String
        });
        self_elements.push(self.inline_term_name_id(id));
        self_elements.push(html! {
            <span class="value">
                {self.inline_term(id,3)}
            </span>
        });
        if let Some(type_id) = self.terms.get_type_id(id) {
            self_elements.push(html! {
                <span class="type">
                    {self.inline_term(type_id, 3)}
                </span>
            });
        };
        if true {
            button_elements.push(html! {
                <button onclick={callback(move || paste_as_reference(id))}>
                    "Paste (ref)"
                </button> : String
            });
            button_elements.push(html! {
                <button onclick={callback(move || insert_lambda(id))}>
                    "Lambda"
                </button> : String
            });
            button_elements.push(html! {
                <button onclick={callback(move || insert_forall(id))}>
                    "ForAll"
                </button> : String
            });
            button_elements.push(html! {
                <button onclick={callback(move || insert_apply(id))}>
                    "Apply"
                </button> : String
            });
        }
        if !matches!(term.contents, TermContents::Nothing) {
            button_elements.push(html! {
                <button onclick={callback(move || clear_term(id))}>
                    "Clear"
                </button> : String
            });
        }
        html! {
            <div class="node" onclick={callback(move || focus_term(id))}>
                //{(focused).then(|| node_parents(term))}
                    {context_elements}
                <div class="self">
                    {self_elements}
                </div>
                <div class="buttons">
                    {button_elements}
                </div>
                //{(depth > 0).then(|| node_children(term, depth - 1))}
            </div> : String
        }
    }

    fn whole_page(&self) -> FlowElement {
        let globals = self.globals();
        //let goals = goals().map(|term| node_element(term, false, 0));
        html! {
            <div class="page">
                {globals}
                {self.node_element(self.focus, true, 2)}
                <div class="goals">
                    //{goals}
                </div>
            </div>
        }
    }

    fn update_gui(&self) {
        quick_and_dirty_web_gui::replace_html(self.whole_page().to_string());
    }
}

static INTERFACE: LazyLock<Mutex<Interface>> = LazyLock::new(|| {
    let args = Args::parse();
    let terms = read_json_file::<_, Environment>(&args.file_path)
        .unwrap_or_else(|_| Environment::with_sorts());
    let focus = *terms.term_variables().next().unwrap().0;
    Mutex::new(Interface {
        file_path: args.file_path,
        terms,
        focus,
        clipboard: focus,
    })
});

fn with_interface(f: impl FnOnce(&mut Interface)) {
    let mut interface = INTERFACE.lock().unwrap();
    f(&mut *interface);
    interface.update_gui();
    write_json_file(&interface.file_path, &interface.terms).unwrap();
}

fn focus_term(id: TermVariableId) {
    with_interface(|interface| {
        interface.focus = id;
    });
}

fn copy_term(id: TermVariableId) {
    with_interface(|interface| {
        interface.clipboard = id;
    });
}

fn use_term(id: TermVariableId) {
    with_interface(|interface| {
        interface.terms.set_to_reference_to(interface.focus, id);
    });
}

fn rename_term(id: TermVariableId, name: String) {
    with_interface(|interface| {
        interface.terms.rename(id, name);
    });
}

fn use_var(id: TermVariableId) {
    with_interface(|interface| {
        interface.terms.set_to_variable_usage(interface.focus, id);
    });
}

fn insert_lambda(id: TermVariableId) {
    with_interface(|interface| {
        interface
            .terms
            .set_to_new_recursive_term(id, RecursiveTermKind::Lambda);
    });
}

fn insert_forall(id: TermVariableId) {
    with_interface(|interface| {
        interface
            .terms
            .set_to_new_recursive_term(id, RecursiveTermKind::ForAll);
    });
}

fn insert_apply(id: TermVariableId) {
    with_interface(|interface| {
        interface
            .terms
            .set_to_new_recursive_term(id, RecursiveTermKind::Apply);
    });
}

fn clear_term(id: TermVariableId) {
    with_interface(|interface| {
        interface.terms.set_to_empty(id);
    });
}

fn paste_as_reference(id: TermVariableId) {
    with_interface(|interface| {
        interface.terms.set_to_reference_to(id, interface.clipboard);
    });
}

fn new_global() {
    with_interface(|interface| {
        let id = interface.terms.create_term_variable();
        interface.focus = id;
    });
}

// fn context_element(context: Context) -> Element {
//     let entries = context.entries().map(|entry| {
//         html! {
//             <div class="entry" onclick={callback(move || focus(id))}>
//                 <div class="name">
//                     {text!("{}", entry.name)}
//                 </div>
//                 <div class="type">
//                     {text!("{}", entry.ty.display())}
//                 </div>
//                 <button onclick={callback(move || put_in_current_goal(entry))}>
//                     Use
//                 </button>
//             </div>
//         }
//     });
//     html! {
//         <div class="context">
//             {entries}
//         </div>
//     }
// }
//
// fn focus(id: TermId) {}
//
// fn node_parents(term: &Node) -> Option<Element> {
//     let active_parent = term.active_parent()?;
//     let parents = term.parents().map(|parent| {
//         html! {
//             <div class="parent" onclick={callback(move || focus(id))}>
//                 <div class="name">
//                     {text!("{}", parent.name)}
//                 </div>
//             </div>
//         }
//     });
//     Some(html! {
//         <div class="parents">
//             <div class="active">
//                 {node_element(active_parent, false, 0)}
//             </div>
//             <div class="other">
//                 {parents}
//             </div>
//         </div>
//     })
// }
//
// fn node_children(term: &Node, depth: usize) -> Element {
//     let children = term.children().map(|child| {
//         node_element(child, depth);
//     });
//     html! {
//         <div class="children">
//             {children}
//         </div>
//     }
// }
//

//
// fn new_global(name: String) {}
//

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
    quick_and_dirty_web_gui::launch(4986).await;
}
