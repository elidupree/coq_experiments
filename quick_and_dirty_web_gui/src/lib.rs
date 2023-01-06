#![feature(once_cell)]

use actix::{Actor, Addr, AsyncContext, Context, Handler, Message, StreamHandler};
use actix_files::NamedFile;
use actix_web::{get, web, App, Error, HttpRequest, HttpResponse, HttpServer, Responder};
use actix_web_actors::ws;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::LazyLock;
use uuid::Uuid;

struct Manager {
    current_html: String,
    current_callbacks: HashMap<String, Box<dyn FnMut(String) + Send>>,
    new_callbacks: HashMap<String, Box<dyn FnMut(String) + Send>>,
    clients: Vec<Addr<Session>>,
}

#[derive(Debug, Message)]
#[rtype(result = "()")]
struct NewClient {
    session: Addr<Session>,
}

#[derive(Message)]
#[rtype(result = "()")]
struct NewCallback {
    id: String,
    callback: Box<dyn FnMut(String) + Send>,
}

#[derive(Clone, Serialize, Debug, Message)]
#[rtype(result = "()")]
enum MessageToClient {
    ReplaceDom(String),
    AppMessage(String),
}

#[derive(Clone, Serialize, Deserialize, Debug, Message)]
#[rtype(result = "()")]
enum MessageFromClient {
    RunCallback(String, String),
}

impl Actor for Manager {
    type Context = Context<Self>;
}

impl Handler<NewClient> for Manager {
    type Result = ();

    fn handle(&mut self, message: NewClient, _context: &mut Self::Context) -> Self::Result {
        message
            .session
            .do_send(MessageToClient::ReplaceDom(self.current_html.clone()));
        self.clients.push(message.session);
    }
}

impl Handler<MessageToClient> for Manager {
    type Result = ();

    fn handle(&mut self, message: MessageToClient, _context: &mut Self::Context) -> Self::Result {
        if let MessageToClient::ReplaceDom(html) = &message {
            self.current_html = html.clone();
            std::mem::swap(&mut self.current_callbacks, &mut self.new_callbacks);
            self.new_callbacks.clear();
        }
        for client in &self.clients {
            client.do_send(message.clone());
        }
    }
}

impl Handler<NewCallback> for Manager {
    type Result = ();

    fn handle(&mut self, message: NewCallback, _context: &mut Self::Context) -> Self::Result {
        self.new_callbacks.insert(message.id, message.callback);
    }
}

impl Handler<MessageFromClient> for Manager {
    type Result = ();

    fn handle(&mut self, message: MessageFromClient, _context: &mut Self::Context) -> Self::Result {
        match message {
            MessageFromClient::RunCallback(id, data) => {
                if let Some(callback) = self.current_callbacks.get_mut(&id) {
                    callback(data)
                }
            }
        }
    }
}

struct WebserverState {
    manager: Addr<Manager>,
}

pub struct Session {
    manager: Addr<Manager>,
}

impl Actor for Session {
    type Context = ws::WebsocketContext<Self>;

    fn started(&mut self, context: &mut Self::Context) {
        self.manager.do_send(NewClient {
            session: context.address(),
        });
    }
}

impl Handler<MessageToClient> for Session {
    type Result = ();

    fn handle(&mut self, message: MessageToClient, context: &mut Self::Context) -> Self::Result {
        context.text(serde_json::to_string(&message).unwrap());
    }
}

impl StreamHandler<Result<ws::Message, ws::ProtocolError>> for Session {
    fn handle(&mut self, msg: Result<ws::Message, ws::ProtocolError>, ctx: &mut Self::Context) {
        match msg {
            Ok(ws::Message::Ping(msg)) => ctx.pong(&msg),
            Ok(ws::Message::Text(text)) => {
                println!("Received from client: {}", text);
                let message = serde_json::from_str::<MessageFromClient>(&text);
                println!("Deserialized: {:?}", message);
                if let Ok(message) = message {
                    self.manager.do_send(message)
                }
            }
            _ => (),
        }
    }
}

#[get("/qadwg_session")]
async fn session(
    req: HttpRequest,
    stream: web::Payload,
    webserver_state: web::Data<WebserverState>,
) -> Result<HttpResponse, Error> {
    ws::start(
        Session {
            manager: webserver_state.manager.clone(),
        },
        &req,
        stream,
    )
}

#[get("/qadwg.js")]
async fn qadwg_script() -> impl Responder {
    concat!(include_str!("qadwg.js"), include_str!("morphdom-umd.js"))
}

#[get("/")]
async fn index() -> impl Responder {
    NamedFile::open_async("./static/index.html").await.unwrap()
}

static MANAGER: LazyLock<Addr<Manager>> = LazyLock::new(|| {
    Manager {
        current_html: "".to_string(),
        current_callbacks: HashMap::new(),
        new_callbacks: HashMap::new(),
        clients: vec![],
    }
    .start()
});

pub async fn launch(port: u16) {
    let state = web::Data::new(WebserverState {
        manager: MANAGER.clone(),
    });

    HttpServer::new(move || {
        App::new()
            .app_data(state.clone())
            .service(index)
            .service(session)
            .service(qadwg_script)
    })
    .workers(1)
    .bind(("localhost", port))
    .unwrap()
    .run()
    .await
    .unwrap();
}

pub fn replace_html(html: String) {
    MANAGER.do_send(MessageToClient::ReplaceDom(html));
}

pub fn send_app_message(message: &impl Serialize) {
    MANAGER.do_send(MessageToClient::AppMessage(
        serde_json::to_string(message).unwrap(),
    ));
}

pub fn callback(mut f: impl FnMut() + Send + 'static) -> String {
    let id = Uuid::new_v4().simple().to_string();
    MANAGER.do_send(NewCallback {
        id: id.clone(),
        callback: Box::new(move |_| f()),
    });
    format!(r##"send_to_socket("RunCallback",[{},""]);"##, id)
}

pub fn callback_with<D: DeserializeOwned>(
    js: &str,
    mut f: impl FnMut(D) + Send + 'static,
) -> String {
    let id = Uuid::new_v4().simple().to_string();
    MANAGER.do_send(NewCallback {
        id: id.clone(),
        callback: Box::new(move |argument| f(serde_json::from_str(&argument).unwrap())),
    });
    format!(r##"send_to_socket("RunCallback",[{},{}]);"##, id, js)
}
