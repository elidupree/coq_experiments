use crate::global_state_types::{Featured, Mode, RocketState, SharedState};
use parking_lot::Mutex;
use rocket::config::{Environment, LoggingLevel};
use rocket::response::NamedFile;
use rocket::{Config, State};
use rocket_contrib::json::Json;
use rocket_contrib::serve::StaticFiles;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use typed_html::dom::DOMTree;
use typed_html::html;

#[get("/")]
fn index(_rocket_state: State<RocketState>) -> Option<NamedFile> {
    NamedFile::open("./static/index.html").ok()
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Debug)]
pub enum InputFromFrontend {
    SetFeatured(Featured),
}

impl Featured {
    pub fn input_string(self) -> String {
        serde_json::to_string(&InputFromFrontend::SetFeatured(self)).unwrap()
    }
}

#[post("/input", data = "<input>")]
fn input(input: Json<InputFromFrontend>, rocket_state: State<RocketState>) {
    let Json(input) = input;
    let mut guard = rocket_state.shared.lock();
    let shared: &mut SharedState = &mut *guard;

    // assume every input might cause a UI change
    shared.last_ui_change_serial_number += 1;

    match input {
        InputFromFrontend::SetFeatured(new_featured) => {
            // gotta check if this input wasn't delayed across a file reload
            if let Some(Mode::ProofMode(p, f)) = &mut shared.known_mode {
                if p.descendant(new_featured.tactics_path_all()).is_some() {
                    *f = new_featured;
                }
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Debug)]
pub struct ContentRequestParameters {
    last_ui_change_serial_number: Option<u64>,
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Debug)]
pub struct ContentResponse {
    last_ui_change_serial_number: u64,
    ui_replacement: Option<String>,
}
#[post("/content", data = "<parameters>")]
fn content(
    parameters: Json<ContentRequestParameters>,
    rocket_state: State<RocketState>,
) -> Json<ContentResponse> {
    let mut guard = rocket_state.shared.lock();
    let shared: &mut SharedState = &mut *guard;

    if parameters.last_ui_change_serial_number == Some(shared.last_ui_change_serial_number) {
        return Json(ContentResponse {
            last_ui_change_serial_number: shared.last_ui_change_serial_number,
            ui_replacement: None,
        });
    }

    let whole_interface_html = shared.whole_interface_html();

    let document: DOMTree<String> = html! {
        <div id="content">
            {whole_interface_html}
        </div>
    };
    let document = document.to_string();
    //eprintln!("Sending to frontend: {}", document);
    Json(ContentResponse {
        last_ui_change_serial_number: shared.last_ui_change_serial_number,
        ui_replacement: Some(document),
    })
}

pub fn launch(shared: Arc<Mutex<SharedState>>) {
    rocket::custom(
        Config::build(Environment::Development)
            .address("localhost")
            .port(3508)
            .log_level(LoggingLevel::Off)
            .unwrap(),
    )
    .mount("/media/", StaticFiles::from("./static/media"))
    .mount("/", routes![index, input, content])
    .manage(RocketState { shared })
    .launch();
}
