#![allow(unused_imports)]

use parking_lot::Mutex;
use rocket::config::{Config, Environment, LoggingLevel};
use rocket::response::NamedFile;
use rocket::State;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{Duration, SystemTime};
//use rocket::response::content::Json;
use rocket_contrib::json::Json;
use std::collections::HashMap;
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::ops::Range;
use std::process::{self, ChildStdin, ChildStdout, Stdio};
use typed_html::dom::DOMTree;
use typed_html::elements::FlowContent;
use typed_html::{html, text};

use crate::serapi_protocol::*;

pub type Element = Box<dyn FlowContent<String>>;

// impl CombatState {
//     pub fn view(&self) -> Element {
//         let monsters = self
//       .monsters
//       .iter()
//       .filter(|monster| !monster.gone)
//       .map(|monster| {
//         html! {
//           <div class="monster">
//             {text! ("{:?} i{} {:?}", monster.monster_id, monster.move_history.last().map_or("?".to_string(), ToString::to_string), monster.creature)}
//           </div>
//         }
//       });
//         let hand = self.hand.iter().map(|card| {
//             html! {
//               <div class="card">
//                 {text! ("{:?}", card)}
//               </div>
//             }
//         });
//         html! {
//           <div class="combat-state">
//             <div class="player">
//               {text! ("({}) {:?}", self.player.energy, self.player.creature)}
//             </div>
//             <div class="monsters">
//               {monsters}
//             </div>
//             <div class="hand">
//               {hand}
//             </div>
//           </div>
//         }
//     }
// }

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Debug)]
pub struct InterfaceState {}

#[derive(Debug)]
pub struct AddedFromFile {
    location_in_file: Range<usize>,
    state_id: StateId,
}
#[derive(Debug)]
pub struct AddedExploratory {
    state_id: StateId,
}
#[derive(Debug)]
pub struct TopState {
    added_from_file: Vec<AddedFromFile>,
    added_exploratory: Vec<AddedExploratory>,
    num_executed_from_file: usize,
    num_executed_exploratory: usize,
    active_command: Option<Command>,
}

#[derive(PartialEq, Eq, Debug)]
pub enum ActiveCommandExtra {
    AddFromFile { offset: usize },
    AddExploratory,
    ExecFromFile { index: usize },
    ExecExploratory { index: usize },
    Other,
}

#[derive(PartialEq, Eq, Debug)]
pub struct ProofState {
    goals: String,
    steps: HashMap<String, ProofState>,
}

#[derive(PartialEq, Eq, Debug)]
pub enum Mode {
    ProofMode(ProofState),
    NotProofMode,
}

#[derive(Debug)]
pub struct ApplicationState {
    child_stdin: ChildStdin,
    code_path: PathBuf,
    current_file_code: String,
    last_added_file_code: String,
    // TODO : this isn't the most efficient file watcher system, figure out what is?
    last_code_modified: Option<SystemTime>,
    active_command_extra: Option<ActiveCommandExtra>,
    error_occurred_during_last_file_exec: bool,
    error_occurred_during_last_exploratory_exec: bool,
    top_state: TopState,
    known_mode: Option<Mode>,
}

#[derive(Debug)]
pub struct RocketState {
    application_state: Arc<Mutex<ApplicationState>>,
    root_path: PathBuf,
}

pub fn send_command(
    application: &mut ApplicationState,
    command: Command,
    extra: ActiveCommandExtra,
) {
    assert!(application.top_state.active_command == None);
    assert!(application.active_command_extra == None);
    let text = serde_lexpr::to_string(&command).unwrap();
    eprintln!("sending command to sertop: {}\n", text);
    writeln!(application.child_stdin, "{}", text).unwrap();
    application.top_state.active_command = Some(command);
    application.active_command_extra = Some(extra);
}

pub fn first_difference_index<T: PartialEq>(a: &[T], b: &[T]) -> Option<usize> {
    a.iter().zip(b).position(|(a, b)| a != b).or_else(|| {
        if a.len() == b.len() {
            None
        } else {
            Some(std::cmp::min(a.len(), b.len()))
        }
    })
}

pub fn frequent_update(application: &mut ApplicationState) {
    // If the code file has been modified, update it.
    if fs::metadata(&application.code_path)
        .and_then(|m| m.modified())
        .ok()
        != application.last_code_modified
    {
        if let Ok(mut code) = fs::read_to_string(&application.code_path) {
            if let Some(index) = code.find("STOP") {
                code.truncate(index);
            }
            application.current_file_code = code;
        }
    }

    // current design: only start doing things if sertop is ready
    if application.top_state.active_command.is_some() {
        return;
    }

    // first priority: make sure coq "Added" state is up-to-date with the file
    let first_difference_offset = first_difference_index(
        application.current_file_code.as_bytes(),
        application.last_added_file_code.as_bytes(),
    );
    if let Some(first_difference_offset) = first_difference_offset {
        // first cancel everything that's been invalidated...
        let mut invalidated = application
            .top_state
            .added_from_file
            .iter()
            .map(|a| (a.state_id, a.location_in_file.end > first_difference_offset))
            .chain(
                application
                    .top_state
                    .added_exploratory
                    .iter()
                    .map(|a| (a.state_id, true)),
            )
            .enumerate()
            .skip_while(|(_index, (_id, invalidated))| !invalidated)
            .map(|(index, (id, _invalidated))| (index, id))
            .peekable();

        if let Some(&(first_invalidated_index, _)) = invalidated.peek() {
            let canceled = invalidated.map(|(_index, id)| id).collect();
            send_command(
                application,
                Command::Cancel(canceled),
                ActiveCommandExtra::Other,
            );
            application.known_mode = None;
            application.top_state.num_executed_exploratory = 0;
            application.error_occurred_during_last_exploratory_exec = false;
            if first_invalidated_index <= application.top_state.num_executed_from_file {
                // i.e. if we invalidated the one that failed to execute, or earlier
                application.error_occurred_during_last_file_exec = false;
                application.top_state.num_executed_from_file = first_invalidated_index;
            }
            return;
        }

        // ...and then add anything that remains
        let (unhandled_file_offset, last_added_id) = application
            .top_state
            .added_from_file
            .last()
            .map_or((0, None), |a| (a.location_in_file.end, Some(a.state_id)));
        let unhandled_file_contents =
            application.current_file_code[unhandled_file_offset..].to_owned();
        application.last_added_file_code = application.current_file_code.clone();
        send_command(
            application,
            Command::Add(
                AddOptions {
                    ontop: last_added_id,
                    ..default()
                },
                unhandled_file_contents,
            ),
            ActiveCommandExtra::AddFromFile {
                offset: unhandled_file_offset,
            },
        );
        return;
    }

    // second priority: make sure coq "Executed" state is as far along as possible
    if application.top_state.num_executed_from_file < application.top_state.added_from_file.len()
        && !application.error_occurred_during_last_file_exec
    {
        send_command(
            application,
            Command::Exec(
                application.top_state.added_from_file[application.top_state.num_executed_from_file]
                    .state_id,
            ),
            ActiveCommandExtra::ExecFromFile {
                index: application.top_state.num_executed_from_file,
            },
        );
        return;
    }
    if application.top_state.num_executed_exploratory
        < application.top_state.added_exploratory.len()
        && !application.error_occurred_during_last_exploratory_exec
    {
        send_command(
            application,
            Command::Exec(
                application.top_state.added_exploratory
                    [application.top_state.num_executed_exploratory]
                    .state_id,
            ),
            ActiveCommandExtra::ExecExploratory {
                index: application.top_state.num_executed_exploratory,
            },
        );
        return;
    }

    // third priority: proof exploration
    let proof_state = match &application.known_mode {
        None => {
            send_command(
                application,
                Command::Query(
                    QueryOptions {
                        sid: application
                            .top_state
                            .added_from_file
                            .last()
                            .map_or(0, |a| a.state_id),
                        pp: FormatOptions {
                            pp_format: PrintFormat::PpStr,
                            ..default()
                        },
                        ..default()
                    },
                    QueryCommand::EGoals,
                ),
                ActiveCommandExtra::Other,
            );
            return;
        }
        Some(Mode::NotProofMode) => return,
        Some(Mode::ProofMode(p)) => p,
    };

    const TACTICS: &[&str] = &[
        "intuition idtac.",
        "intro.",
        "intros.",
        "split.",
        "reflexivity.",
    ];
}

#[post("/content", data = "<interface_state>")]
fn content(interface_state: Json<InterfaceState>, rocket_state: State<RocketState>) -> String {
    let mut guard = rocket_state.application_state.lock();
    let application = &mut *guard;

    let proof_state_representation = match &application.known_mode {
        None => text!("Processing..."),
        Some(Mode::NotProofMode) => text!("Not in proof mode"),
        Some(Mode::ProofMode(p)) => text!("{}", p.goals),
    };

    let document: DOMTree<String> = html! {
      <div id="content">
        {proof_state_representation}
      </div>
    };
    document.to_string()
}

#[get("/default_interface_state")]
fn default_interface_state() -> Json<InterfaceState> {
    Json(InterfaceState {
    //client_placeholder: 3,
    //placeholder_i32: 5,
    //placeholder_string: "whatever".to_string()
  })
}

#[get("/")]
fn index(rocket_state: State<RocketState>) -> Option<NamedFile> {
    NamedFile::open(rocket_state.root_path.join("static/index.html")).ok()
}

#[get("/media/<file..>")]
fn media(file: PathBuf, rocket_state: State<RocketState>) -> Option<NamedFile> {
    NamedFile::open(rocket_state.root_path.join("static/media/").join(file)).ok()
}

pub fn receiver_thread(child_stdout: ChildStdout, application_state: Arc<Mutex<ApplicationState>>) {
    for line in BufReader::new(child_stdout).lines() {
        let line = line.unwrap();
        let parsed = serde_lexpr::parse::from_str(&line);
        let parsed = match parsed {
            Ok(parsed) => parsed,
            Err(err) => {
                eprintln!(
                    "received invalid S-expression from sertop ({:?}):\n{}\n",
                    err, line
                );
                continue;
            }
        };
        let interpreted: Result<Answer, _> = serde_lexpr::from_value(&parsed); //serde_lexpr::from_str(&line.replace("(", " ("));

        let interpreted = match interpreted {
            Ok(interpreted) => interpreted,
            Err(err) => {
                eprintln!(
                    "received invalid Answer from sertop ({:?}):\n{}\n{}\n",
                    err, parsed, line,
                );
                continue;
            }
        };
        eprintln!(
            "received valid input from sertop:\n{:?}\n{}\n",
            interpreted, line
        );

        let mut guard = application_state.lock();
        let application: &mut ApplicationState = &mut *guard;
        #[allow(clippy::single_match)]
        match interpreted {
            Answer::Feedback(feedback) => match feedback.contents {
                FeedbackContent::Processed => {}
                _ => {}
            },
            Answer::Answer(_command_tag, answer_kind) => match answer_kind {
                AnswerKind::Added(state_id, location, _extra) => {
                    match &application.active_command_extra {
                        Some(ActiveCommandExtra::AddFromFile { offset }) => {
                            application.top_state.added_from_file.push(AddedFromFile {
                                location_in_file: offset + location.bp as usize
                                    ..offset + location.ep as usize,
                                state_id,
                            });
                        }
                        Some(ActiveCommandExtra::AddExploratory) => {
                            application
                                .top_state
                                .added_exploratory
                                .push(AddedExploratory { state_id });
                        }
                        _ => panic!("received Added when we weren't doing an Add"),
                    }
                }
                AnswerKind::Canceled(state_ids) => {
                    application.top_state.added_from_file.retain(|added| {
                        state_ids.iter().all(|canceled| &added.state_id != canceled)
                    });
                    application.top_state.added_exploratory.retain(|added| {
                        state_ids.iter().all(|canceled| &added.state_id != canceled)
                    });
                }
                AnswerKind::CoqExn(_) => match &application.active_command_extra {
                    Some(ActiveCommandExtra::ExecFromFile { .. }) => {
                        application.error_occurred_during_last_file_exec = true;
                    }
                    Some(ActiveCommandExtra::ExecExploratory { .. }) => {
                        application.error_occurred_during_last_exploratory_exec = true;
                    }
                    _ => {}
                },
                AnswerKind::ObjList(objects) => match &application.top_state.active_command {
                    Some(Command::Query(_, QueryCommand::EGoals)) => {
                        if application.known_mode == None {
                            application.known_mode = Some(match objects.first() {
                                Some(CoqObject::CoqString(goals)) => Mode::ProofMode(ProofState {
                                    goals: goals.clone(),
                                    steps: HashMap::new(),
                                }),
                                _ => Mode::NotProofMode,
                            });
                        }
                    }
                    _ => {}
                },
                AnswerKind::Completed => {
                    let command = application
                        .top_state
                        .active_command
                        .take()
                        .expect("received Completed when no command was running?");
                    let extra = application
                        .active_command_extra
                        .take()
                        .expect("active_command_extra not set for a command?");
                    match (command, extra) {
                        (_, ActiveCommandExtra::ExecFromFile { .. }) => {
                            if !application.error_occurred_during_last_file_exec {
                                application.top_state.num_executed_from_file += 1;
                            }
                        }
                        (_, ActiveCommandExtra::ExecExploratory { .. }) => {
                            if !application.error_occurred_during_last_exploratory_exec {
                                application.top_state.num_executed_exploratory += 1;
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            },
        }
    }
}

pub fn processing_thread(application_state: Arc<Mutex<ApplicationState>>) {
    // let mut guard = application_state.lock();
    // send_command(
    //     &mut guard.child_stdin,
    //     &Command::Add(
    //         Default::default(),
    //         "Lemma foo : forall x : nat, x = x.".to_string(),
    //     ),
    // );
    // send_command(
    //     &mut guard.child_stdin,
    //     &Command::Add(
    //         Default::default(),
    //         "Lemma foo : forall x : nat, x = x.".to_string(),
    //     ),
    // );
    // send_command(&mut guard.child_stdin, &Command::Exec(2));

    loop {
        let mut guard = application_state.lock();
        frequent_update(&mut *guard);
        std::mem::drop(guard);
        std::thread::sleep(Duration::from_millis(10));
    }
}

pub fn run(root_path: PathBuf, code_path: PathBuf) {
    let child = process::Command::new("sertop")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("failed sertop command");
    let child_stdout = child.stdout.expect("no stdout?");
    let child_stdin = child.stdin.expect("no stdin?");

    let application_state = ApplicationState {
        child_stdin,
        code_path,
        current_file_code: String::new(),
        last_added_file_code: String::new(),
        last_code_modified: None,
        active_command_extra: None,
        error_occurred_during_last_file_exec: false,
        error_occurred_during_last_exploratory_exec: false,
        top_state: TopState {
            added_from_file: Vec::new(),
            added_exploratory: Vec::new(),
            num_executed_from_file: 0,
            num_executed_exploratory: 0,
            active_command: None,
        },
        known_mode: None,
    };

    let application_state = Arc::new(Mutex::new(application_state));

    std::thread::spawn({
        let application_state = application_state.clone();
        move || {
            receiver_thread(child_stdout, application_state);
        }
    });

    std::thread::spawn({
        let application_state = application_state.clone();
        move || {
            processing_thread(application_state);
        }
    });

    rocket::custom(
        Config::build(Environment::Development)
            .address("localhost")
            .port(3508)
            .log_level(LoggingLevel::Off)
            .unwrap(),
    )
    .mount("/", routes![index, media, content, default_interface_state])
    .manage(RocketState {
        application_state,
        root_path,
    })
    .launch();
}
