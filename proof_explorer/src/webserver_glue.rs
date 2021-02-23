use crate::global_state_types::{
    Featured, MessageFromOutsideSertop, MessageToMainThread, RocketState, SharedState,
};
use rocket::config::{Environment, LoggingLevel};
use rocket::response::NamedFile;
use rocket::{Config, State};
use rocket_contrib::json::Json;
use rocket_contrib::serve::StaticFiles;
use serde::{Deserialize, Serialize};
use typed_html::dom::DOMTree;
use typed_html::html;

#[get("/")]
fn index(_rocket_state: State<RocketState>) -> Option<NamedFile> {
    NamedFile::open("./static/index.html").ok()
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Debug)]
pub enum MessageFromFrontend {
    SetFeatured(Featured),
}

impl Featured {
    pub fn input_string(self) -> String {
        serde_json::to_string(&MessageFromFrontend::SetFeatured(self)).unwrap()
    }
}

#[allow(clippy::unit_arg)] // why is this needed? no idea, probably rocket proc macro stuff
#[post("/input", data = "<input>")]
fn input(input: Json<MessageFromFrontend>, rocket_state: State<RocketState>) {
    let Json(input) = input;

    // assume every input might cause a UI change
    rocket_state.shared.lock().last_ui_change_serial_number += 1;
    rocket_state
        .sender
        .lock()
        .send(MessageToMainThread::FromOutsideSertop(
            MessageFromOutsideSertop::FromFrontend(input),
        ))
        .expect("main thread should never drop receiver");
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

pub fn launch(state: RocketState) {
    rocket::custom(
        Config::build(Environment::Development)
            .address("localhost")
            .port(3508)
            .log_level(LoggingLevel::Off)
            .unwrap(),
    )
    .mount("/media/", StaticFiles::from("./static/media"))
    .mount("/", routes![index, input, content])
    .manage(state)
    .launch();
}
