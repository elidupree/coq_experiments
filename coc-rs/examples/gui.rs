#![feature(array_chunks)]
#![feature(once_cell)]

use coc_rs::term::RecursiveTermKind;
use coc_rs::term_variable::{Environment, Sort, TermTypeAndValue, TermValue, TermVariableId};
use quick_and_dirty_web_gui::{callback, callback_with};
use std::sync::{LazyLock, Mutex};
use typed_html::elements::{FlowContent, PhrasingContent};
use typed_html::{elements, html, text};

pub type FlowElement = Box<dyn FlowContent<String>>;
pub type PhrasingElement = Box<dyn PhrasingContent<String>>;
pub type Span = Box<elements::span<String>>;

struct Interface {
    terms: Environment,
    focus: TermVariableId,
    clipboard: Option<TermTypeAndValue>,
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
        if name.len() < 3 {
            name.extend(
                abc.into_iter()
                    .take(3 - name.len())
                    .map(|a| char::from_u32(((a as u32) & 63) + 63).unwrap()),
            );
        }
        let style =
            format!("color: hwb({h1}turn 0.0% {b}%); background-color: hwb({h2}turn {w}% 0.0%)");

        html! {
            <span class="term_name_id" style=style>
                {text!(name)}
            </span>
        }
    }
    fn inline_term(&self, id: TermVariableId, depth_limit: usize) -> Span {
        let body: Span = match &self.terms.get_term(id).type_and_value {
            None => {
                html! {
                    <span class="hole">
                        "_"
                    </span>
                }
            }
            Some(TermTypeAndValue { value, .. }) => match value {
                TermValue::VariableUsage(v) => {
                    html! {
                        <span class="variable-usage">
                            "$"
                            {self.inline_term_name_id(*v)}
                        </span>
                    }
                }
                TermValue::Sort(sort) => {
                    let name = match sort {
                        Sort::Prop => "P",
                        Sort::Type => "T",
                    };
                    html! {
                        <span class="sort">
                            {text!(name)}
                        </span>
                    }
                }
                TermValue::Recursive(kind, child_ids) => {
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
                                let body = self.inline_term(child_ids[1], depth_limit - 1);
                                html! {
                                    <span class="abstraction">
                                        {text!(sigil)}
                                        {var}
                                        ", "
                                        {body}
                                    </span>
                                }
                            }
                            Apply => {
                                let f = self.inline_term(child_ids[0], depth_limit - 1);
                                let arg = self.inline_term(child_ids[1], 1);
                                html! {
                                    <span class="application">
                                        "("
                                        {f}
                                        " "
                                        {arg}
                                        ")"
                                    </span>
                                }
                            }
                        }
                    }
                }
            },
        };
        body
    }
    fn global(&self, id: TermVariableId) -> FlowElement {
        let g = self.terms.get_term(id);
        let ty = g.type_and_value.as_ref().map(|t| {
            html! {
                <span class="type">
                    {self.inline_term(t.type_id, 3)}
                </span>
            }
        });
        html! {
            <div class="global" onclick={callback(move || focus_term(id))}>
                <div class="spec">
                    {self.inline_term_name_id(id)}
                    <span class="value">
                        {self.inline_term(id, 3)}
                    </span>
                    {ty}
                </div>
                <div class="buttons">
                    <button onclick={callback(move || copy_term(id))}>
                        "Copy"
                    </button>
                </div>
            </div> : String
        }
    }

    fn globals(&self) -> FlowElement {
        let mut named_globals = Vec::new();
        let mut other_terms = Vec::new();
        for (&id, term) in self.terms.term_variables() {
            if term.name != "" {
                named_globals.push((id, term));
            } else if term.back_references.is_empty() {
                other_terms.push((id, term));
            }
        }
        named_globals.sort_by_key(|&(id, term)| (term.name.clone(), id));
        other_terms.sort_by_key(|&(id, _term)| id);
        let individual_globals = named_globals
            .into_iter()
            .chain(other_terms)
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

    fn whole_page(&self) -> FlowElement {
        let globals = self.globals();
        //let goals = goals().map(|term| node_element(term, false, 0));
        html! {
            <div class="page">
                {globals}
                //{node_element(active_node(), true, 2)}
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
    let terms = Environment::with_sorts();
    let focus = *terms.term_variables().next().unwrap().0;
    Mutex::new(Interface {
        terms,
        focus,
        clipboard: None,
    })
});

fn with_interface(f: impl FnOnce(&mut Interface)) {
    let mut interface = INTERFACE.lock().unwrap();
    f(&mut *interface);
    interface.update_gui();
}

fn focus_term(id: TermVariableId) {
    with_interface(|interface| {
        interface.focus = id;
    });
}

fn copy_term(id: TermVariableId) {
    with_interface(|interface| {
        interface.clipboard = interface.terms.get_term(id).type_and_value.clone();
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
// fn node_element(term: &Node, focused: bool, depth: usize) -> Element {
//     let id = term.id;
//     let mut elements: Vec<Element> = Vec::new();
//     if focused {
//         elements.push(context_element(term));
//     }
//     elements.push(html! {
//         <div class="name">
//             {text!("{}", g.name)}
//         </div>
//     });
//     elements.push(html! {
//         <div class="value">
//             {text!("{}", g.value.display())}
//         </div>
//     });
//     elements.push(html! {
//         <div class="type">
//             {text!("{}", g.ty.display())}
//         </div>
//     });
//     if something {
//         elements.push(html! {
//             <button onclick={callback(move || insert_lambda(id))}>
//                 Lambda
//             </button>
//         });
//         elements.push(html! {
//             <button onclick={callback(move || insert_forall(id))}>
//                 ForAll
//             </button>
//         });
//         elements.push(html! {
//             <button onclick={callback(move || insert_apply(id))}>
//                 Apply
//             </button>
//         });
//     }
//     if something {
//         elements.push(html! {
//             <button onclick={callback(move || clear(id))}>
//                 Clear
//             </button>
//         });
//     }
//     html! {
//         <div class="node" onclick={callback(move || focus(id))}>
//             {(focused).then(|| node_parents(term))}
//             <div class="self" onclick={callback(move || focus(id))}>
//                 {elements}
//             </div>
//             {(depth > 0).then(|| node_children(term, depth - 1))}
//         </div>
//     }
// }
//
// fn new_global(name: String) {}
//
#[actix_web::main]
async fn main() {
    with_interface(|_| {});
    quick_and_dirty_web_gui::launch(4986).await;
}
