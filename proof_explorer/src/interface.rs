#![allow(unused_imports, clippy::collapsible_else_if)]

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
use std::io::{BufRead, BufReader, Write};
use std::ops::Range;
use std::process::{self, ChildStdin, ChildStdout, Stdio};
use std::{fs, mem};
use typed_html::dom::DOMTree;
use typed_html::elements::FlowContent;
use typed_html::{html, text};

use crate::serapi_protocol::*;

pub type Element = Box<dyn FlowContent<String>>;

/*

Autorun design:

The default proof exploration root is the last command from the file that successfully executes.

Before we can try commands one at a time, we must parse them; in order to post them, we must Add all of them. Some of them may have parse errors, meaning the "Added commands" don't cover the entire file; subsequent to Adding them, some of them may fail to execute. Thus, the proof exploration root may before the last Added command.

I don't currently understand the parallelism or DAG nature of the API, so I'm going to proceed with the simple assumptions that (1) commands must be executed in file order, and (2) we have to Cancel any failed-to-execute commands before we can Add exploratory commands the precede them. Thus, proof exploration can only proceed if the set of Added commands equals the set of executed commands.

When the file changes, we potentially need to update the proof exploration root. Any Added commands that have changed definitely need to be canceled; if we had made it to the proof exploration stage, then all Added commands are before the proof exploration root, so it's definitely invalidated. The other way to invalidate a proof exploration root is if all the commands before it are still valid, but one after it has *newly become* valid. If there was *never* a successfully Added successor to the current root, then we always need to perform an Add to check whether there are new valid ones; if there *was* a successfully Added (but unsuccessfully executed) successor to the current root, then we only need to update if *that* command was touched by the file changes.

Thus:
- if end_of_first_added_from_file_that_failed_to_execute is `Some(i)`, then there remain no Added commands after `i`, and a change that is *not before* `i` requires no action.
- if we have reached proof exploration state (i.e. all added_from_file have been executed) and any file change occurs that is not excluded by the above, then that necessitates reverting all synthetic commands, reverting all added_from_file that are not entirely before the change, and Adding all parts of the file that are after the last added_from_file.
- if we have not reached proof exploration state (i.e. there some added_from_file that have not been executed), then there is technically no need to cancel the unexecuted commands until we get to them: if we hit an execution error, we'll be canceling them anyway. This caveat from the SerAPI docs is relevant: "In particular, [Cancel] will force execution up to the previous sentence; thus it is not possible to parse a list of sentences and then replace them without incurring in the cost of executing them." So we would prefer to only Cancel when we are cancelling everything after the latest command that has successfully executed.

Thus, the priorities are:
1) first, if there is any added_from_file command that is consistent with the current file but not executed, execute it.
2) otherwise, if there are any added_from_file commands after the latest executed command, Cancel all of them.
3) mutually exclusive with those first two, if there are any *executed* commands that are inconsistent with the current file, cancel them.
4) otherwise, if the current file differs from the most-recently-Added version of the file at any position not excluded by end_of_first_added_from_file_that_failed_to_execute, Add the rest of the current file.
5) otherwise, we are ready for proof exploration.

Separately, any time the collection of executed statements *changes*, we need to forget what we know about the proof state. That happens unconditionally in (3), and might happen in (1) (but can be deferred until we know the execution didn't error).

 */

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Debug)]
pub struct InterfaceState {}

#[derive(Debug)]
pub struct AddedFromFile {
    location_in_file: Range<usize>,
    state_id: StateId,
}

#[derive(Debug)]
pub struct AddedSynthetic {
    code: String,
    state_id: StateId,
}

#[derive(Debug)]
pub struct TopState {
    added_from_file: Vec<AddedFromFile>,
    added_synthetic: Vec<AddedSynthetic>,
    num_executed_from_file: usize,
    num_executed_synthetic: usize,
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
    end_of_first_added_from_file_that_failed_to_execute: Option<usize>,
    error_occurred_during_last_exploratory_exec: bool,

    top_state: TopState,

    known_mode: Option<Mode>,
}

#[derive(Debug)]
pub struct RocketState {
    application_state: Arc<Mutex<ApplicationState>>,
    root_path: PathBuf,
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

impl TopState {
    fn last_added(&self) -> Option<StateId> {
        self.added_synthetic
            .last()
            .map(|a| a.state_id)
            .or_else(|| self.added_from_file.last().map(|a| a.state_id))
    }
}

impl ApplicationState {
    pub fn send_command(&mut self, command: Command, extra: ActiveCommandExtra) {
        assert!(self.top_state.active_command == None);
        assert!(self.active_command_extra == None);
        let text = serde_lexpr::to_string(&command).unwrap();
        eprintln!("sending command to sertop: {}\n", text);
        writeln!(self.child_stdin, "{}", text).unwrap();
        self.top_state.active_command = Some(command);
        self.active_command_extra = Some(extra);
    }

    pub fn frequent_update(&mut self) {
        // If the code file has been modified, update it.
        if fs::metadata(&self.code_path)
            .and_then(|m| m.modified())
            .ok()
            != self.last_code_modified
        {
            if let Ok(mut code) = fs::read_to_string(&self.code_path) {
                if let Some(index) = code.find("STOP") {
                    code.truncate(index);
                }
                self.current_file_code = code;
            }
        }

        // current design: only start doing things if sertop is ready
        if self.top_state.active_command.is_some() {
            return;
        }

        let first_difference_offset = first_difference_index(
            self.current_file_code.as_bytes(),
            self.last_added_file_code.as_bytes(),
        );

        // First, if a file change has invalidated anything that was actually executed,
        // cancel it all and forget the proof state.
        if let Some(first_difference_offset) = first_difference_offset {
            let mut need_to_cancel = self.top_state.added_from_file
                [..self.top_state.num_executed_from_file]
                .last()
                .map_or(false, |a| a.location_in_file.end > first_difference_offset);
            if need_to_cancel {
                // In this case, it's possible that there are also synthetic commands left,
                // which we'd need to clean up
                let canceled = self
                    .top_state
                    .added_from_file
                    .iter()
                    .filter(|a| a.location_in_file.end > first_difference_offset)
                    .map(|a| a.state_id)
                    .chain(self.top_state.added_synthetic.iter().map(|a| a.state_id))
                    .collect();

                self.send_command(Command::Cancel(canceled), ActiveCommandExtra::Other);
                return;
            }
        }

        // Otherwise, execute anything we've already added, as long as it's still
        // consistent with the file and hasn't already hit an execution error.
        if self
            .end_of_first_added_from_file_that_failed_to_execute
            .is_none()
        {
            if let Some(next) = self
                .top_state
                .added_from_file
                .get(self.top_state.num_executed_from_file)
            {
                // There should never be synthetic commands while there are
                // still unexecuted ones from the file. Make sure of this.
                assert!(self.top_state.added_synthetic.is_empty());

                if first_difference_offset.map_or(true, |i| next.location_in_file.end <= i) {
                    self.send_command(
                        Command::Exec(
                            self.top_state.added_from_file[self.top_state.num_executed_from_file]
                                .state_id,
                        ),
                        ActiveCommandExtra::ExecFromFile {
                            index: self.top_state.num_executed_from_file,
                        },
                    );
                    return;
                }
            }
        }

        // After the above, if there are any unexecuted commands from the file, cancel them.
        // (Since they either threw errors or are inconsistent with the current file.)
        if let Some(first_difference_offset) = first_difference_offset {
            let canceled: Vec<_> = self.top_state.added_from_file
                [self.top_state.num_executed_from_file..]
                .iter()
                .map(|a| a.state_id)
                .collect();
            if !canceled.is_empty() {
                // There should never be synthetic commands while there are
                // still unexecuted ones from the file. Make sure of this.
                assert!(self.top_state.added_synthetic.is_empty());

                self.send_command(Command::Cancel(canceled), ActiveCommandExtra::Other);
                return;
            }

            // Finally, if the file has changed, then we need to Add the remaining part,
            // UNLESS that part is after the first execution error from the file,
            // in which case we don't have to care about it yet.
            if self
                .end_of_first_added_from_file_that_failed_to_execute
                .map_or(true, |i| first_difference_offset < i)
            {
                let (unhandled_file_offset, last_added_id) = self
                    .top_state
                    .added_from_file
                    .last()
                    .map_or((0, None), |a| (a.location_in_file.end, Some(a.state_id)));
                let unhandled_file_contents =
                    self.current_file_code[unhandled_file_offset..].to_owned();
                self.last_added_file_code = self.current_file_code.clone();
                self.send_command(
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
        }

        // If we reach this point in the code, we are ready for proof exploration
        self.do_proof_exploration();
    }

    fn try_tactic(&mut self, tactic: String) {
        self.send_command(
            Command::Add(
                AddOptions {
                    ontop: self.top_state.last_added(),
                    ..default()
                },
                tactic,
            ),
            ActiveCommandExtra::AddExploratory,
        );
    }

    fn query_goals(&mut self) {
        self.send_command(
            Command::Query(
                QueryOptions {
                    sid: self.top_state.last_added().unwrap_or(0),
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
    }

    fn revert_to_proof_exploration_root(&mut self) {
        self.send_command(
            Command::Cancel(
                self.top_state
                    .added_synthetic
                    .iter()
                    .map(|a| a.state_id)
                    .collect(),
            ),
            ActiveCommandExtra::Other,
        );
        self.top_state.num_executed_synthetic = 0;
        self.error_occurred_during_last_exploratory_exec = false;
    }

    fn do_proof_exploration(&mut self) {
        let proof_state = match self.known_mode {
            None => {
                self.query_goals();
                return;
            }
            Some(Mode::NotProofMode) => return,
            Some(Mode::ProofMode(ref p)) => p,
        };

        if !self.error_occurred_during_last_exploratory_exec {
            // If we're in the middle of trying a tactic, execute it.
            if let Some(next) = self
                .top_state
                .added_synthetic
                .get(self.top_state.num_executed_synthetic)
            {
                let id = next.state_id;
                self.send_command(
                    Command::Exec(id),
                    ActiveCommandExtra::ExecExploratory {
                        index: self.top_state.num_executed_synthetic,
                    },
                );
                return;
            }

            // if it's been executed but not goal-queried, goal-query it.
            if let Some(last) = self.top_state.added_synthetic.last() {
                if proof_state.steps.get(&last.code).is_none() {
                    self.query_goals();
                    return;
                }
            }
        }

        // if it hit an error or was already goal-queried, revert it.
        if !self.top_state.added_synthetic.is_empty() {
            self.revert_to_proof_exploration_root();
            return;
        }

        const TACTICS: &[&str] = &[
            "intuition idtac.",
            "intro.",
            "intros.",
            "split.",
            "reflexivity.",
        ];

        for &tactic in TACTICS {
            if proof_state.steps.get(tactic).is_none() {
                self.try_tactic(tactic.to_string());
                return;
            }
        }
    }
}

#[post("/content", data = "<interface_state>")]
fn content(interface_state: Json<InterfaceState>, rocket_state: State<RocketState>) -> String {
    let mut guard = rocket_state.application_state.lock();
    let application = &mut *guard;

    let proof_state_representation: Element = match &application.known_mode {
        None => text!("Processing..."),
        Some(Mode::NotProofMode) => text!("Not in proof mode"),
        Some(Mode::ProofMode(p)) => {
            let steps = p.steps.iter().map(|(tactic, p2)| {
                html! {
                    <div class="step">
                        <div class="tactic">
                            <pre>{text!("{}", tactic)}</pre>
                        </div>
                        <div class="step_goal">
                            <pre>{text!("{}", p2.goals)}</pre>
                        </div>
                    </div>
                }
            });
            html! {
                <div class="proof_state">
                    <div class="proof_root">
                        <pre>{text!("{}", p.goals)}</pre>
                    </div>
                    <div class="proof_steps">
                        {steps}
                    </div>
                </div>
            }
        }
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
        eprintln!("received valid input from sertop: {:?}\n", interpreted);

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
                    match (
                        &application.top_state.active_command,
                        &application.active_command_extra,
                    ) {
                        (_, Some(ActiveCommandExtra::AddFromFile { offset })) => {
                            application.top_state.added_from_file.push(AddedFromFile {
                                location_in_file: offset + location.bp as usize
                                    ..offset + location.ep as usize,
                                state_id,
                            });
                        }
                        (Some(Command::Add(_, code)), Some(ActiveCommandExtra::AddExploratory)) => {
                            application.top_state.added_synthetic.push(AddedSynthetic {
                                code: code.clone(),
                                state_id,
                            });
                        }
                        _ => panic!("received Added when we weren't doing an Add"),
                    }
                }
                AnswerKind::Canceled(state_ids) => {
                    application.top_state.added_from_file.retain(|added| {
                        state_ids.iter().all(|canceled| &added.state_id != canceled)
                    });
                    application.top_state.added_synthetic.retain(|added| {
                        state_ids.iter().all(|canceled| &added.state_id != canceled)
                    });
                    if application.top_state.added_from_file.len()
                        < application.top_state.num_executed_from_file
                    {
                        application.top_state.num_executed_from_file =
                            application.top_state.added_from_file.len();
                        application.end_of_first_added_from_file_that_failed_to_execute = None;
                        application.known_mode = None;
                    }
                    if application.top_state.added_synthetic.len()
                        < application.top_state.num_executed_synthetic
                    {
                        application.top_state.num_executed_synthetic =
                            application.top_state.added_synthetic.len();
                        application.error_occurred_during_last_exploratory_exec = false;
                    }
                }
                AnswerKind::CoqExn(_) => {
                    match &application.active_command_extra {
                        Some(ActiveCommandExtra::ExecFromFile { index }) => {
                            application.end_of_first_added_from_file_that_failed_to_execute = Some(
                                application.top_state.added_from_file[*index]
                                    .location_in_file
                                    .end,
                            );
                        }
                        Some(ActiveCommandExtra::ExecExploratory { .. }) => {
                            application.error_occurred_during_last_exploratory_exec = true;
                            let proof_state = match &mut application.known_mode
                        {Some(Mode::ProofMode(p)) =>p, _ => panic!("shouldn't be doing exploratory execution when not in proof mode"),
                        };
                            proof_state.steps.insert(
                                application
                                    .top_state
                                    .added_synthetic
                                    .last()
                                    .unwrap()
                                    .code
                                    .clone(),
                                ProofState {
                                    goals: "failed".to_string(),
                                    steps: HashMap::new(),
                                },
                            );
                        }
                        _ => {}
                    }
                }
                AnswerKind::ObjList(objects) => match &application.top_state.active_command {
                    Some(Command::Query(_, QueryCommand::EGoals)) => match &mut application
                        .known_mode
                    {
                        None => {
                            application.known_mode = Some(match objects.first() {
                                Some(CoqObject::CoqString(goals)) => Mode::ProofMode(ProofState {
                                    goals: goals.clone(),
                                    steps: HashMap::new(),
                                }),
                                _ => Mode::NotProofMode,
                            });
                        }
                        Some(Mode::NotProofMode) => panic!(
                            "shouldn't have queried goals when known not to be in proof mode"
                        ),
                        Some(Mode::ProofMode(p)) => {
                            let goals = match objects.first() {
                                Some(CoqObject::CoqString(goals)) => goals,
                                _ => panic!(
                                    "sertop didn't send any goals after tactic while in proof mode"
                                ),
                            };
                            p.steps.insert(
                                application
                                    .top_state
                                    .added_synthetic
                                    .last()
                                    .unwrap()
                                    .code
                                    .clone(),
                                ProofState {
                                    goals: goals.clone(),
                                    steps: HashMap::new(),
                                },
                            );
                        }
                    },
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
                            if application
                                .end_of_first_added_from_file_that_failed_to_execute
                                .is_none()
                            {
                                application.top_state.num_executed_from_file += 1;
                                application.known_mode = None;
                            }
                        }
                        (_, ActiveCommandExtra::ExecExploratory { .. }) => {
                            if !application.error_occurred_during_last_exploratory_exec {
                                application.top_state.num_executed_synthetic += 1;
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
    loop {
        let mut guard = application_state.lock();
        guard.frequent_update();
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
        end_of_first_added_from_file_that_failed_to_execute: None,
        error_occurred_during_last_exploratory_exec: false,
        top_state: TopState {
            added_from_file: Vec::new(),
            added_synthetic: Vec::new(),
            num_executed_from_file: 0,
            num_executed_synthetic: 0,
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
