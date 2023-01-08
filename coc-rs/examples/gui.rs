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
        let id_characters: Vec<_> =
            id.0.as_u128()
                .to_le_bytes()
                .array_chunks::<5>()
                .take(3)
                .map(|&[a, h, b, bh, bw]| {
                    let h = (h as f64) / 255.0;
                    let b = ((b as f64) / 255.0).powi(3);
                    let bh = (bh as f64) / 255.0;
                    let bw = 0.7 + ((bw as f64) / 255.0).powi(2) * 0.3;
                    let a = char::from_u32(((a as u32) & 63) + 63).unwrap();
                    let style = format!("color: hwb({h} 0.0 {b}); color: hwb({bh} {bw} 0.0)");
                    html! {
                        <span style=style>
                            {text!("{}", a)}
                        </span>
                    }
                })
                .collect();
        html! {
            <span class="term-name-id">
                <span class="name">
                    {text!(name)}
                </span>
                <span class="id">
                    {id_characters}
                </span>
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
        let ty = g
            .type_and_value
            .as_ref()
            .map(|t| self.inline_term(t.type_id, 3));
        html! {
            <div class="global" onclick={callback(move || focus_term(id))}>
                <div class="name">
                    {text!(&g.name)}
                </div>
                <div class="value">
                    {self.inline_term(id, 3)}
                </div>
                <div class="type">
                    {ty}
                </div>
                <button onclick={callback(move || copy_term(id))}>
                    "Copy"
                </button>
            </div> : String
        }
    }

    fn whole_page(&self) -> FlowElement {
        //let globals = globals();
        //let goals = goals().map(|term| node_element(term, false, 0));
        html! {
            <div class="page">
                <div class="globals">
                    //{globals}
                </div>
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
// fn globals() -> Element {
//     let individual_globals = context.globals.iter().map(|g| global(g));
//     html! {
//         <div class="globals">
//             {individual_globals}
//             <div class="new_global">
//                 <input id="new_global_name" type="text"/>
//                 <button onclick={callback_with(r##"$("#new_global_name").value"##, new_global)}>
//                     Create
//                 </button>
//             </div>
//         </div>
//     }
// }
//
#[actix_web::main]
async fn main() {
    with_interface(|_| {});
    quick_and_dirty_web_gui::launch(4986).await;
}
