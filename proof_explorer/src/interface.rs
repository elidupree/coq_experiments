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
use std::default::default;
use std::fmt::Debug;
use std::io::{BufRead, BufReader, Write};
use std::ops::Range;
use std::process::{self, ChildStdin, ChildStdout, Stdio};
use std::{fs, mem};
use typed_html::dom::DOMTree;
use typed_html::elements::FlowContent;
use typed_html::{html, text};

use crate::serapi_protocol::{
    AddOptions, Answer, AnswerKind, Command, ConstrExpr, CoqObject, FeedbackContent, FormatOptions,
    PrintFormat, QueryCommand, QueryOptions, ReifiedGoal, SerGoals, StateId,
};

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

#[allow(unused)]
pub trait CommandRunner: Send + Sync + 'static {
    fn handle_answer(&mut self, application: &mut ApplicationState, answer: &AnswerKind) {}
    fn finish(self: Box<Self>, application: &mut ApplicationState) {}
}

#[derive(PartialEq, Eq, Debug)]
pub struct ProofState {
    goals_string: String,
    goals_ser: SerGoals<ReifiedGoal<ConstrExpr>>,
    attempted_tactics: HashMap<String, TacticResult>,
}

#[derive(PartialEq, Eq, Debug)]
pub enum TacticResult {
    Success(ProofState),
    Failure,
}

#[derive(PartialEq, Eq, Debug)]
pub enum Mode {
    ProofMode(ProofState),
    NotProofMode,
}

pub struct ApplicationState {
    child_stdin: ChildStdin,

    code_path: PathBuf,
    current_file_code: String,
    last_added_file_code: String,
    // TODO : this isn't the most efficient file watcher system, figure out what is?
    last_code_modified: Option<SystemTime>,

    active_command_runner: Option<Box<dyn CommandRunner>>,
    end_of_first_added_from_file_that_failed_to_execute: Option<usize>,

    top_state: TopState,

    known_mode: Option<Mode>,
}

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

impl ProofState {
    pub fn descendant<'a>(&self, mut tactics: impl Iterator<Item = &'a str>) -> &ProofState {
        match tactics.next() {
            None => self,
            Some(tactic) => match self.attempted_tactics.get(tactic) {
                Some(TacticResult::Success(child)) => child.descendant(tactics),
                Some(TacticResult::Failure) => {
                    panic!("attempted to descend into tactic that failed")
                }
                None => panic!("attempted to descend into a tactic that was never checked"),
            },
        }
    }
    pub fn descendant_mut<'a>(
        &mut self,
        mut tactics: impl Iterator<Item = &'a str>,
    ) -> &mut ProofState {
        match tactics.next() {
            None => self,
            Some(tactic) => match self.attempted_tactics.get_mut(tactic) {
                Some(TacticResult::Success(child)) => child.descendant_mut(tactics),
                Some(TacticResult::Failure) => {
                    panic!("attempted to descend into tactic that failed")
                }
                None => panic!("attempted to descend into a tactic that was never checked"),
            },
        }
    }
}

impl ApplicationState {
    pub fn send_command(&mut self, command: Command, runner: impl CommandRunner) {
        assert_eq!(self.top_state.active_command, None);
        assert!(self.active_command_runner.is_none());
        let text = serde_lexpr::to_string(&command).unwrap();
        eprintln!("sending command to sertop: {}\n", text);
        writeln!(self.child_stdin, "{}", text).unwrap();
        self.top_state.active_command = Some(command);
        self.active_command_runner = Some(Box::new(runner));
    }

    pub fn cancel(&mut self, canceled: Vec<StateId>) {
        #[derive(Debug)]
        struct CancelRunner;
        impl CommandRunner for CancelRunner {
            fn handle_answer(&mut self, application: &mut ApplicationState, answer: &AnswerKind) {
                if let AnswerKind::Canceled(state_ids) = answer {
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
                    }
                }
            }
        }

        self.send_command(Command::Cancel(canceled), CancelRunner);
    }

    pub fn exec_next_from_file(&mut self) {
        #[derive(Debug)]
        struct ExecFromFileRunner {
            index: usize,
        }
        impl CommandRunner for ExecFromFileRunner {
            fn handle_answer(&mut self, application: &mut ApplicationState, answer: &AnswerKind) {
                if let AnswerKind::CoqExn(_) = answer {
                    application.end_of_first_added_from_file_that_failed_to_execute = Some(
                        application.top_state.added_from_file[self.index]
                            .location_in_file
                            .end,
                    );
                }
            }
            fn finish(self: Box<Self>, application: &mut ApplicationState) {
                if application
                    .end_of_first_added_from_file_that_failed_to_execute
                    .is_none()
                {
                    application.top_state.num_executed_from_file += 1;
                    application.known_mode = None;
                }
            }
        }

        // There should never be synthetic commands while there are
        // still unexecuted ones from the file. Make sure of this.
        assert!(self.top_state.added_synthetic.is_empty());

        self.send_command(
            Command::Exec(
                self.top_state.added_from_file[self.top_state.num_executed_from_file].state_id,
            ),
            ExecFromFileRunner {
                index: self.top_state.num_executed_from_file,
            },
        );
    }

    pub fn add_rest_of_file(&mut self) {
        #[derive(Debug)]
        struct AddFromFileRunner {
            offset: usize,
        }
        impl CommandRunner for AddFromFileRunner {
            fn handle_answer(&mut self, application: &mut ApplicationState, answer: &AnswerKind) {
                if let AnswerKind::Added(state_id, location, _extra) = answer {
                    application.top_state.added_from_file.push(AddedFromFile {
                        location_in_file: self.offset + location.bp as usize
                            ..self.offset + location.ep as usize,
                        state_id: *state_id,
                    });
                }
            }
        }

        let (unhandled_file_offset, last_added_id) = self
            .top_state
            .added_from_file
            .last()
            .map_or((0, None), |a| (a.location_in_file.end, Some(a.state_id)));
        let unhandled_file_contents = self.current_file_code[unhandled_file_offset..].to_owned();
        self.last_added_file_code = self.current_file_code.clone();
        self.send_command(
            Command::Add(
                AddOptions {
                    ontop: last_added_id,
                    ..default()
                },
                unhandled_file_contents,
            ),
            AddFromFileRunner {
                offset: unhandled_file_offset,
            },
        );
    }

    fn query_goals(&mut self) {
        #[derive(Debug)]
        struct QueryGoalsStringRunner {
            received_goals_string: Option<String>,
        }
        impl CommandRunner for QueryGoalsStringRunner {
            fn handle_answer(&mut self, application: &mut ApplicationState, answer: &AnswerKind) {
                let objects = if let AnswerKind::ObjList(objects) = answer {
                    objects
                } else {
                    return;
                };
                match objects.first() {
                    Some(CoqObject::CoqString(goals_string)) => {
                        self.received_goals_string = Some(goals_string.clone())
                    }
                    _ => match application.known_mode {
                        None => {
                            application.known_mode = Some(Mode::NotProofMode);
                        }
                        Some(Mode::NotProofMode) => panic!(
                            "shouldn't have queried goals when known not to be in proof mode"
                        ),
                        Some(Mode::ProofMode(_)) => panic!(
                            "sertop was supposed to send goals as a CoqString, but sent {:?}",
                            objects
                        ),
                    },
                };
            }
            fn finish(self: Box<Self>, application: &mut ApplicationState) {
                if let Some(goals_string) = self.received_goals_string {
                    application.send_command(
                        Command::Query(
                            QueryOptions {
                                sid: application.top_state.last_added().unwrap_or(0),
                                pp: FormatOptions {
                                    pp_format: PrintFormat::PpSer,
                                    ..default()
                                },
                                ..default()
                            },
                            QueryCommand::EGoals,
                        ),
                        QueryGoalsSerRunner { goals_string },
                    );
                }
            }
        }

        #[derive(Debug)]
        struct QueryGoalsSerRunner {
            goals_string: String,
        }
        impl CommandRunner for QueryGoalsSerRunner {
            fn handle_answer(&mut self, application: &mut ApplicationState, answer: &AnswerKind) {
                let objects = if let AnswerKind::ObjList(objects) = answer {
                    objects
                } else {
                    return;
                };
                let goals_ser = match objects.first() {
                    Some(CoqObject::CoqExtGoal(goals_ser)) => goals_ser,
                    _ => panic!("sertop sent goals string, but didn't send goals ser - huh?"),
                };
                let new_proof_state = ProofState {
                    goals_string: self.goals_string.clone(),
                    goals_ser: goals_ser.clone(),
                    attempted_tactics: HashMap::new(),
                };
                match &mut application.known_mode {
                    None => {
                        application.known_mode = Some(Mode::ProofMode(new_proof_state));
                    }
                    Some(Mode::NotProofMode) => {
                        panic!("shouldn't have even gotten to QueryGoalsSerRunner when known not to be in proof mode")
                    }
                    Some(Mode::ProofMode(p)) => {
                        assert_eq!(application.top_state.num_executed_synthetic, application.top_state.added_synthetic.len());
                        // Note: can't use application.latest_proof_state_mut() here because the application would believe we have already gotten to this spot
                        let tactics : &[AddedSynthetic] = &application.top_state.added_synthetic;
                        let latest = tactics.last().expect("if the proof state already exists, we should only be querying goals after a tactic").code.clone();
                        let p2 = p.descendant_mut (tactics [..tactics.len()-1].iter().map(|t|t.code.as_str()));
                        let insert_result = p2.attempted_tactics.insert(latest,TacticResult::Success(new_proof_state));
                        assert!(insert_result.is_none(), "shouldn't have queried goals for a tactic that was already tested");
                    }
                }
            }
        }
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
            QueryGoalsStringRunner {
                received_goals_string: None,
            },
        );
    }

    pub fn run_tactic(&mut self, tactic: String) {
        #[derive(Debug)]
        struct AddSyntheticRunner {
            exception_happened: bool,
        }
        impl CommandRunner for AddSyntheticRunner {
            fn handle_answer(&mut self, application: &mut ApplicationState, answer: &AnswerKind) {
                let code =
                    if let Some(Command::Add(_, code)) = &application.top_state.active_command {
                        code.clone()
                    } else {
                        panic!("command doesn't match runner");
                    };
                match answer {
                    AnswerKind::Added(state_id, _location, _extra) => {
                        application.top_state.added_synthetic.push(AddedSynthetic {
                            code,
                            state_id: *state_id,
                        });
                    }
                    AnswerKind::CoqExn(_exn) => {
                        self.exception_happened = true;
                        assert_eq!(
                            application.top_state.num_executed_synthetic,
                            application.top_state.added_synthetic.len()
                        );
                        let insert_result = application
                            .latest_proof_state_mut()
                            .attempted_tactics
                            .insert(code, TacticResult::Failure);
                        assert!(
                            insert_result.is_none(),
                            "shouldn't have added a tactic that was already tested and failed"
                        );
                    }
                    _ => {}
                }
            }
            fn finish(self: Box<Self>, application: &mut ApplicationState) {
                if !self.exception_happened {
                    application.send_command(
                        Command::Exec(
                            application.top_state.added_synthetic
                                [application.top_state.num_executed_synthetic]
                                .state_id,
                        ),
                        ExecSyntheticRunner {
                            exception_happened: false,
                        },
                    );
                }
            }
        }

        #[derive(Debug)]
        struct ExecSyntheticRunner {
            exception_happened: bool,
        }
        impl CommandRunner for ExecSyntheticRunner {
            fn handle_answer(&mut self, application: &mut ApplicationState, answer: &AnswerKind) {
                if let AnswerKind::CoqExn(_exn) = answer {
                    self.exception_happened = true;
                    assert_eq!(
                        application.top_state.num_executed_synthetic + 1,
                        application.top_state.added_synthetic.len()
                    );
                    let latest = application
                        .top_state
                        .added_synthetic
                        .last()
                        .expect("if we're executing a tactic, it should have been added")
                        .code
                        .clone();
                    let insert_result = application
                        .latest_proof_state_mut()
                        .attempted_tactics
                        .insert(latest, TacticResult::Failure);
                    assert!(
                        insert_result.is_none(),
                        "shouldn't have queried goals for a tactic that was already tested"
                    );
                }
            }
            fn finish(self: Box<Self>, application: &mut ApplicationState) {
                if !self.exception_happened {
                    application.top_state.num_executed_synthetic += 1;
                    application.query_goals();
                }
            }
        }
        self.send_command(
            Command::Add(
                AddOptions {
                    ontop: self.top_state.last_added(),
                    ..default()
                },
                tactic,
            ),
            AddSyntheticRunner {
                exception_happened: false,
            },
        );
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
            let need_to_cancel = self.top_state.added_from_file
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

                self.cancel(canceled);
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
                if first_difference_offset.map_or(true, |i| next.location_in_file.end <= i) {
                    self.exec_next_from_file();
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

                self.cancel(canceled);
                return;
            }

            // Finally, if the file has changed, then we need to Add the remaining part,
            // UNLESS that part is after the first execution error from the file,
            // in which case we don't have to care about it yet.
            if self
                .end_of_first_added_from_file_that_failed_to_execute
                .map_or(true, |i| first_difference_offset < i)
            {
                self.add_rest_of_file();
                return;
            }
        }

        // If we reach this point in the code, we are ready for proof exploration
        self.do_proof_exploration();
    }

    fn root_proof_state_mut(&mut self) -> &mut ProofState {
        match &mut self.known_mode {
            Some(Mode::ProofMode(p)) => p,
            _ => panic!("assumed we were in proof mode when we weren't"),
        }
    }

    fn latest_proof_state_mut(&mut self) -> &mut ProofState {
        let root = match &mut self.known_mode {
            Some(Mode::ProofMode(p)) => p,
            _ => panic!("assumed we were in proof mode when we weren't"),
        };
        root.descendant_mut(
            self.top_state.added_synthetic[..self.top_state.num_executed_synthetic]
                .iter()
                .map(|t| t.code.as_str()),
        )
    }

    fn revert_to_proof_exploration_root(&mut self) {
        self.cancel(
            self.top_state
                .added_synthetic
                .iter()
                .map(|a| a.state_id)
                .collect(),
        );
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

        // for now: always test from the root
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
            if proof_state.attempted_tactics.get(tactic).is_none() {
                self.run_tactic(tactic.to_string());
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
            let mut successful_tactics = Vec::new();
            let mut failed_tactics = Vec::new();
            for (tactic, result) in &p.attempted_tactics {
                match result {
                    TacticResult::Success(successor) => {
                        let element = html! {
                            <div class="successful_tactic">
                                <div class="tactic">
                                    <pre>{text!("{}", tactic)}</pre>
                                </div>
                                <div class="step_goal">
                                    <pre>{text!("{}", successor.goals_string)}</pre>
                                </div>
                            </div>
                        };
                        successful_tactics.push(element);
                    }
                    TacticResult::Failure => {
                        let element = html! {
                            <div class="failed_tactic">
                                <pre>{text!("{}: failed", tactic)}</pre>
                            </div>
                        };
                        failed_tactics.push(element);
                    }
                }
            }
            html! {
                <div class="proof_state">
                    <div class="proof_root">
                        <pre>{text!("{}", p.goals_string)}</pre>
                    </div>
                    <div class="proof_steps">
                        {successful_tactics}
                        {failed_tactics}
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
            Answer::Feedback(_feedback) => {}
            Answer::Answer(_command_tag, answer_kind) => {
                // We have to take it and put it back so that we can
                // hand it both &mut self and &mut application
                let mut runner = application
                    .active_command_runner
                    .take()
                    .expect("active_command_extra not set for a command?");
                runner.handle_answer(application, &answer_kind);
                if let AnswerKind::Completed = answer_kind {
                    let _command = application
                        .top_state
                        .active_command
                        .take()
                        .expect("received Completed when no command was running?");
                    runner.finish(application);
                // and don't put it back if it's finished
                } else {
                    application.active_command_runner = Some(runner);
                }
            }
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
        active_command_runner: None,
        end_of_first_added_from_file_that_failed_to_execute: None,
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
