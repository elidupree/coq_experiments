#![feature(array_chunks)]
#![feature(once_cell)]

use clap::Parser;
use coc_rs::constructors::Constructors;
use coc_rs::metavariable::{Environment, MetavariableId};
use coc_rs::utils::{read_json_file, write_json_file};
use quick_and_dirty_web_gui::{callback, callback_with};
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

impl Interface {
    fn inline_metavariable_name_id(&self, id: MetavariableId) -> Span {
        let name = &self.environment.get(id).name;
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
            <span class="metavariable_name_id" style=style onclick={callback(move || focus_node(id))}>
                {text!(name)}
            </span> : String
        }
    }

    fn node_element(&self, id: MetavariableId) -> FlowElement {
        let metavariable = self.environment.get(id);
        let type_definition = Constructors::coc()
            .types
            .get(&metavariable.typename)
            .unwrap();
        let validity = self.environment.local_validity(id);
        let mut self_elements: Vec<FlowElement> = Vec::new();
        let mut child_elements: Vec<FlowElement> = Vec::new();
        let name_element_id = format!("metavariable_{}_name", id.0);
        self_elements.push(html! {
            <input id=Id::new(&*name_element_id) type="text" value=&metavariable.name
              oninput={callback_with(
                &format!(r##"document.getElementById("{name_element_id}").value"##),
                move |name: String| rename_metavariable (id,name)
            )} /> : String
        });
        self_elements.push(html! {
            <button onclick={callback(move || use_metavariable(id))}>
                "Use"
            </button> : String
        });
        self_elements.push(self.inline_metavariable_name_id(id));
        match &metavariable.constructor {
            None => {
                for (constructor_name, _) in type_definition.constructors.iter() {
                    let text = text!(constructor_name);
                    let constructor_name = constructor_name.clone();
                    child_elements.push(html! {
                        <button onclick={callback(move || set_constructor(id,Some (constructor_name)))}>
                            {text}
                        </button> : String
                    });
                }
            }
            Some(constructor) => {
                child_elements.push(html! {
                    <button onclick={callback(move || set_constructor(id,None))}>
                        "Remove constructor"
                    </button> : String
                });
            }
        }
        html! {
            <div class="node" onclick={callback(move || focus_node(id))}>
                <div class="self">
                    {self_elements}
                </div>
                <div class="children">
                    {child_elements}
                </div>
            </div> : String
        }
    }
    fn nodes(&self) -> FlowElement {
        let nodes = self
            .environment
            .metavariables()
            .map(|(&id, _)| self.node_element(id));
        html! {
            <div class="nodes">
                {nodes}
            </div>
        }
    }
    fn whole_page(&self) -> FlowElement {
        let nodes = self.nodes();
        let new_buttons = Constructors::coc().types.keys().cloned().map(|typename| {
            html! {
                <div class="new_global">
                    <button onclick={callback(|| new_global(typename))}>
                        "New global"
                    </button>
                </div> : String
            }
        });
        html! {
            <div class="page">
                {new_buttons}
                {nodes}
            </div>
        }
    }

    fn update_gui(&self) {
        quick_and_dirty_web_gui::replace_html(self.whole_page().to_string());
    }

    fn focus_node(&mut self, id: MetavariableId) {
        self.focus = Some((id, None));
    }
}

static INTERFACE: LazyLock<Mutex<Interface>> = LazyLock::new(|| {
    let args = Args::parse();
    let environment = read_json_file::<_, Environment>(&args.file_path)
        .unwrap_or_else(|_| Environment::default());
    let focus = *environment.metavariables().next().unwrap().0;
    Mutex::new(Interface {
        file_path: args.file_path,
        environment,
        focus: None,
    })
});

fn with_interface(f: impl FnOnce(&mut Interface)) {
    let mut interface = INTERFACE.lock().unwrap();
    f(&mut *interface);
    interface.update_gui();
    write_json_file(&interface.file_path, &interface.environment).unwrap();
}

fn focus_node(id: MetavariableId) {
    with_interface(|interface: &mut Interface| {
        interface.focus_node(id);
    });
}

fn set_constructor(id: MetavariableId, constructor: Option<String>) {
    with_interface(|interface: &mut Interface| {
        interface.environment.set_constructor(id, constructor);
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
                    interface
                        .environment
                        .set_data_argument(focus_id, index, Some(id));
                }
                WhichChild::Precondition(index) => {
                    interface
                        .environment
                        .set_precondition(focus_id, index, Some(id));
                }
            }
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
        interface.focus_node(id);
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
    quick_and_dirty_web_gui::launch(4986).await;
}
