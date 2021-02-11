#![allow(unused_imports, clippy::collapsible_else_if)]

use derivative::Derivative;
use difference::{Changeset, Difference};
use parking_lot::Mutex;
use rocket::config::{Config, Environment, LoggingLevel};
use rocket::response::NamedFile;
use rocket::State;
use rocket_contrib::json::Json;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::default::default;
use std::fmt::Debug;
use std::io::{BufRead, BufReader, Write};
use std::ops::Range;
use std::path::PathBuf;
use std::process::{self, ChildStdin, ChildStdout, Stdio};
use std::sync::Arc;
use std::time::{Duration, SystemTime};
use std::{fs, iter, mem};
use typed_html::dom::DOMTree;
use typed_html::elements::FlowContent;
use typed_html::{html, text};
//use rocket::response::content::Json;

use crate::goals_analysis::{CoqValueInfo, Goals};
use crate::serapi_protocol::{
    AddOptions, Answer, AnswerKind, Command, ConstrExpr, CoqObject, FeedbackContent, FormatOptions,
    IdenticalHypotheses, NamesId, PrintFormat, PrintOptions, QueryCommand, QueryOptions,
    ReifiedGoal, SerGoals, StateId,
};
use crate::tactics::Tactic;

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

#[derive(Debug)]
pub struct AddedFromFile {
    location_in_file: Range<usize>,
    state_id: StateId,
}

#[derive(Debug)]
pub struct AddedSynthetic {
    tactic: Tactic,
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
    goals: Goals<CoqValueInfo>,
    attempted_tactics: HashMap<Tactic, TacticResult>,
}

#[derive(PartialEq, Eq, Debug)]
pub enum TacticResult {
    Success(ProofState),
    Failure,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize, Derivative)]
#[derivative(Default)]
pub enum FeaturedInState {
    #[derivative(Default)]
    Nothing,
    Hypothesis {
        name: String,
        subterm: Option<Range<usize>>,
    },
    Conclusion {
        subterm: Option<Range<usize>>,
    },
}

// I was going to call this "focused", but that term is already used
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default, Serialize, Deserialize)]
pub struct Featured {
    featured_in_root: FeaturedInState,
    tactics: Vec<(Tactic, FeaturedInState)>,
    num_tactics_run: usize,
}

#[derive(PartialEq, Eq, Debug)]
pub enum Mode {
    ProofMode(ProofState, Featured),
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

    last_ui_change_serial_number: u64,
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

impl Featured {
    pub fn tactics_path(&self) -> impl Iterator<Item = &Tactic> {
        self.tactics_path_all().take(self.num_tactics_run)
    }
    pub fn tactics_path_all(&self) -> impl Iterator<Item = &Tactic> {
        self.tactics.iter().map(|(t, _)| t)
    }
    pub fn featured_in_current(&self) -> &FeaturedInState {
        match self.num_tactics_run.checked_sub(1) {
            Some(i) => &self.tactics[i].1,
            None => &self.featured_in_root,
        }
    }
    pub fn featured_in_current_mut(&mut self) -> &mut FeaturedInState {
        match self.num_tactics_run.checked_sub(1) {
            Some(i) => &mut self.tactics[i].1,
            None => &mut self.featured_in_root,
        }
    }
    pub fn extended(&self, tactic: Tactic) -> Featured {
        Featured {
            tactics: self
                .tactics
                .iter()
                .take(self.num_tactics_run)
                .cloned()
                .chain(iter::once((tactic, FeaturedInState::Nothing)))
                .collect(),
            num_tactics_run: self.num_tactics_run + 1,
            ..self.clone()
        }
    }

    fn input_string(self) -> String {
        serde_json::to_string(&Input::SetFeatured(self)).unwrap()
    }
}

impl ProofState {
    pub fn child(&self, tactic: &Tactic) -> Option<&ProofState> {
        match self.attempted_tactics.get(tactic) {
            Some(TacticResult::Success(child)) => Some(child),
            _ => None,
        }
    }
    pub fn child_mut(&mut self, tactic: &Tactic) -> Option<&mut ProofState> {
        match self.attempted_tactics.get_mut(tactic) {
            Some(TacticResult::Success(child)) => Some(child),
            _ => None,
        }
    }
    pub fn descendant<'a>(
        &self,
        mut tactics: impl Iterator<Item = &'a Tactic>,
    ) -> Option<&ProofState> {
        match tactics.next() {
            None => Some(self),
            Some(tactic) => self
                .child(tactic)
                .and_then(|child| child.descendant(tactics)),
        }
    }
    pub fn descendant_mut<'a>(
        &mut self,
        mut tactics: impl Iterator<Item = &'a Tactic>,
    ) -> Option<&mut ProofState> {
        match tactics.next() {
            None => Some(self),
            Some(tactic) => self
                .child_mut(tactic)
                .and_then(|child| child.descendant_mut(tactics)),
        }
    }
}

const GLOBAL_TACTICS: &str = "intro.intros.intuition idtac.split.reflexivity.assumption.constructor.exfalso.instantiate.contradiction.discriminate.trivial.inversion_sigma.symmetry.simpl in *.left.right.classical_left.classical_right.solve_constraints.simplify_eq.subst.cbv.lazy.vm_compute.native_compute.red.hnf.cbn.injection.decide equality.tauto.dtauto.congruence.firstorder.easy.auto.eauto.auto with *.eauto with *.";

const HYPOTHESIS_TACTICS: &str = "simpl in H.cbv in H.injection H.apply H.simple apply H.eapply H.rapply H.lapply H.clear H.revert H.decompose sum H.decompose record H.generalize H.generalize dependent H.absurd H.contradiction H.contradict H.destruct H.case H.induction H.dependent destruction H.dependent induction H.inversion H.discriminate H.inversion_clear H.dependent inversion H.symmetry in H.simplify_eq H.rewrite <- H. rewrite -> H.rewrite <- H in *. rewrite -> H in *.dependent rewrite <- H. dependent rewrite -> H.";

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
        struct QueryGoalsRunner {
            received_goals: Option<Goals<ConstrExpr>>,
        }
        impl CommandRunner for QueryGoalsRunner {
            fn handle_answer(&mut self, application: &mut ApplicationState, answer: &AnswerKind) {
                let objects = if let AnswerKind::ObjList(objects) = answer {
                    objects
                } else {
                    return;
                };
                match objects.first() {
                    Some(CoqObject::CoqExtGoal(goals)) => self.received_goals = Some(goals.clone()),
                    _ => match application.known_mode {
                        None => {
                            application.known_mode = Some(Mode::NotProofMode);
                        }
                        Some(Mode::NotProofMode) => panic!(
                            "shouldn't have queried goals when known not to be in proof mode"
                        ),
                        Some(Mode::ProofMode(_, _)) => panic!(
                            "sertop was supposed to send goals as a CoqString, but sent {:?}",
                            objects
                        ),
                    },
                };
            }
            fn finish(self: Box<Self>, application: &mut ApplicationState) {
                if let Some(goals) = self.received_goals {
                    let iter = goals.goals.clone().into_iter().flat_map(|g| {
                        iter::once(g.ty)
                            .chain(g.hyp.into_iter().flat_map(|h| iter::once(h.2).chain(h.1)))
                    });
                    Box::new(PrintGoalsRunner {
                        goals,
                        iter,
                        current: None,
                        collected: HashMap::new(),
                    })
                    .finish(application);
                }
            }
        }

        #[derive(Debug)]
        struct PrintGoalsRunner<I> {
            goals: Goals<ConstrExpr>,
            iter: I,
            current: Option<ConstrExpr>,
            collected: HashMap<ConstrExpr, String>,
        }
        impl<I: Iterator<Item = ConstrExpr> + Send + Sync + 'static> CommandRunner for PrintGoalsRunner<I> {
            fn handle_answer(&mut self, _application: &mut ApplicationState, answer: &AnswerKind) {
                let objects = if let AnswerKind::ObjList(objects) = answer {
                    objects
                } else {
                    return;
                };
                let string = match objects.first() {
                    Some(CoqObject::CoqString(string)) => string,
                    _ => panic!("unexpected response to Print"),
                };
                self.collected
                    .insert(self.current.take().unwrap(), string.clone());
            }
            fn finish(mut self: Box<Self>, application: &mut ApplicationState) {
                if let Some(unused) = self.current.take() {
                    panic!("Didn't receive printed representation for {:?}?", unused);
                }
                if let Some(next) = self.iter.next() {
                    self.current = Some(next.clone());
                    application.send_command(
                        Command::Print(
                            PrintOptions {
                                sid: application.top_state.last_added().unwrap_or(0),
                                pp: FormatOptions {
                                    pp_format: PrintFormat::PpStr,
                                    pp_margin: 9999999,
                                    ..default()
                                },
                            },
                            CoqObject::CoqExpr(next),
                        ),
                        *self,
                    );
                } else {
                    let collected = self.collected;
                    let new_proof_state = ProofState {
                        goals: self.goals.map_values(|constr_expr| {
                            // note: can't be efficient using `remove` here because there might be duplicates
                            let string = collected.get(&constr_expr).unwrap().clone();
                            CoqValueInfo {
                                constr_expr,
                                string,
                            }
                        }),
                        attempted_tactics: HashMap::new(),
                    };
                    match &mut application.known_mode {
                        None => {
                            application.known_mode = Some(Mode::ProofMode(new_proof_state, Featured::default()));
                        }
                        Some(Mode::NotProofMode) => {
                            panic!("shouldn't have even gotten to QueryGoalsSerRunner when known not to be in proof mode")
                        }
                        Some(Mode::ProofMode(p,_)) => {
                            assert_eq!(application.top_state.num_executed_synthetic, application.top_state.added_synthetic.len());
                            // Note: can't use application.latest_proof_state_mut() here because the application would believe we have already gotten to this spot
                            let tactics : &[AddedSynthetic] = &application.top_state.added_synthetic;
                            let latest = tactics.last().expect("if the proof state already exists, we should only be querying goals after a tactic").tactic.clone();
                            let p2 = p.descendant_mut (tactics [..tactics.len()-1].iter().map(|t|&t.tactic)).unwrap();
                            let insert_result = p2.attempted_tactics.insert(latest,TacticResult::Success(new_proof_state));
                            assert!(insert_result.is_none(), "shouldn't have queried goals for a tactic that was already tested");
                        }
                    }
                }
            }
        }
        self.send_command(
            Command::Query(
                QueryOptions {
                    sid: self.top_state.last_added().unwrap_or(0),
                    pp: FormatOptions {
                        pp_format: PrintFormat::PpSer,
                        ..default()
                    },
                    ..default()
                },
                QueryCommand::EGoals,
            ),
            QueryGoalsRunner {
                received_goals: None,
            },
        );
    }

    pub fn run_tactic(&mut self, tactic: Tactic) {
        #[derive(Debug)]
        struct AddSyntheticRunner {
            tactic: Tactic,
            exception_happened: bool,
        }
        impl CommandRunner for AddSyntheticRunner {
            fn handle_answer(&mut self, application: &mut ApplicationState, answer: &AnswerKind) {
                match answer {
                    AnswerKind::Added(state_id, _location, _extra) => {
                        application.top_state.added_synthetic.push(AddedSynthetic {
                            tactic: self.tactic.clone(),
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
                            .unwrap()
                            .attempted_tactics
                            .insert(self.tactic.clone(), TacticResult::Failure);
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
                            tactic: self.tactic,
                            exception_happened: false,
                        },
                    );
                }
            }
        }

        #[derive(Debug)]
        struct ExecSyntheticRunner {
            tactic: Tactic,
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
                    let insert_result = application
                        .latest_proof_state_mut()
                        .unwrap()
                        .attempted_tactics
                        .insert(self.tactic.clone(), TacticResult::Failure);
                    assert!(
                        insert_result.is_none(),
                        "shouldn't have queried goals for a tactic that was already tested"
                    );
                }
            }
            fn finish(self: Box<Self>, application: &mut ApplicationState) {
                if !self.exception_happened {
                    application.top_state.num_executed_synthetic += 1;
                    if application.latest_proof_state_mut().is_none() {
                        application.query_goals();
                    }
                }
            }
        }
        self.send_command(
            Command::Add(
                AddOptions {
                    ontop: self.top_state.last_added(),
                    ..default()
                },
                tactic.coq_string(),
            ),
            AddSyntheticRunner {
                tactic,
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

    fn latest_proof_state_mut(&mut self) -> Option<&mut ProofState> {
        let root = match &mut self.known_mode {
            Some(Mode::ProofMode(p, _)) => p,
            _ => return None,
        };
        root.descendant_mut(
            self.top_state.added_synthetic[..self.top_state.num_executed_synthetic]
                .iter()
                .map(|t| &t.tactic),
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

    fn featured_state(&self) -> Option<(&ProofState, &FeaturedInState)> {
        let (proof_root, featured): (&ProofState, &Featured) = match &self.known_mode {
            Some(Mode::ProofMode(p, f)) => (p, f),
            _ => return None,
        };
        Some((
            proof_root.descendant(featured.tactics_path()).unwrap(),
            featured.featured_in_current(),
        ))
    }

    fn do_proof_exploration(&mut self) {
        let (proof_root, featured): (&ProofState, &Featured) = match self.known_mode {
            None => {
                self.query_goals();
                return;
            }
            Some(Mode::NotProofMode) => return,
            // note: we have to use `ref` instead of matching on &
            // because otherwise we got lifetime errors from the None branch
            Some(Mode::ProofMode(ref p, ref f)) => (p, f),
        };
        let tactics_path: Vec<_> = featured.tactics_path().collect();
        let featured_state = proof_root.descendant(tactics_path.iter().copied()).unwrap();
        let featured_in_state = featured.featured_in_current();

        // make sure we are currently at the featured proof path before exploring
        let canceled: Vec<_> = self
            .top_state
            .added_synthetic
            .iter()
            .enumerate()
            .skip_while(|(i, a)| tactics_path.get(*i) == Some(&&a.tactic))
            .map(|(_, a)| a.state_id)
            .collect();

        if !canceled.is_empty() {
            self.cancel(canceled);
            return;
        }
        if let Some(next_catchup_tactic) = tactics_path.get(self.top_state.added_synthetic.len()) {
            let tactic = (*next_catchup_tactic).to_owned();
            self.run_tactic(tactic);
            return;
        }

        for tactic in GLOBAL_TACTICS.split_inclusive(".") {
            let tactic = Tactic::from_string(tactic.to_string());
            if featured_state.attempted_tactics.get(&tactic).is_none() {
                self.run_tactic(tactic);
                return;
            }
        }

        if let FeaturedInState::Hypothesis {
            name: featured_name,
            subterm: _,
        } = featured_in_state
        {
            if let Some(goal) = featured_state.goals.goals.first() {
                for IdenticalHypotheses(names, _, _) in &goal.hyp {
                    for NamesId::Id(name) in names {
                        if name == featured_name {
                            for tactic_h in HYPOTHESIS_TACTICS.split_inclusive(".") {
                                let tactic = tactic_h.replace("H", name);
                                let tactic = Tactic::from_string(tactic);
                                if featured_state.attempted_tactics.get(&tactic).is_none() {
                                    self.run_tactic(tactic);
                                    return;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

impl ApplicationState {
    fn attempted_tactics_html(&self, featured: &Featured) -> Element {
        let (featured_state, _) = self.featured_state().unwrap();
        let first_goal = match featured_state.goals.goals.first() {
            Some(goal) => goal,
            None => {
                return text!(
                "All goals solved! (Except maybe shelved goals, I haven't implemented that yet)."
            )
            }
        };
        let featured_hypotheses_string = first_goal.hypothesis_strings().join("\n");
        let featured_conclusion_string = &first_goal.ty.string;

        let mut successful_tactics = Vec::new();
        let mut failed_tactics = Vec::new();
        'tactics: for (tactic, result) in &featured_state.attempted_tactics {
            let successor = match result {
                TacticResult::Success(successor) => successor,
                TacticResult::Failure => {
                    let element = html! {
                        <div class="failed_tactic">
                            <pre>{text!("{}: failed", tactic.human_string())}</pre>
                        </div>
                    };
                    failed_tactics.push(element);
                    continue;
                }
            };

            // these usually won't be exactly equal because evar numbers are different?
            // if successor.goals == featured.goals {
            //     let element = html! {
            //         <div class="failed_tactic">
            //             <pre>{text!("{}: no effect", tactic)}</pre>
            //         </div>
            //     };
            //     failed_tactics.push(element);
            //     continue;
            // }

            let relevant_goals = &successor.goals.goals
                [..successor.goals.goals.len() + 1 - featured_state.goals.goals.len()];
            for goal in relevant_goals {
                let hypotheses_string = goal.hypothesis_strings().join("\n");
                let conclusion_string = &goal.ty.string;
                if hypotheses_string == featured_hypotheses_string
                    && conclusion_string == featured_conclusion_string
                {
                    // If any goal is the same as before, we are no better off;
                    // but a slightly different message is desirable if we also spawned extra goals
                    let text = if successor.goals.goals.len() == featured_state.goals.goals.len() {
                        text!("{}: no effect", tactic.human_string())
                    } else {
                        text!(
                            "{}: spawned new goal, but one was identical to before",
                            tactic.human_string()
                        )
                    };
                    let element = html! {
                        <div class="failed_tactic">
                            <pre>{text}</pre>
                        </div>
                    };
                    failed_tactics.push(element);
                    continue 'tactics;
                }
            }

            let onclick = featured.extended(tactic.clone()).input_string();
            let element = html! {
                <div class="successful_tactic" data-onclick={onclick}>
                    <div class="tactic">
                        <pre>{text!("{}", tactic.human_string())}</pre>
                    </div>
                    {featured_state.goals.diff_html(&successor.goals)}
                </div>
            };
            successful_tactics.push(element);
        }
        html! {
            <div class="attempted_tactics">
                {successful_tactics}
                {failed_tactics}
            </div>
        }
    }
    fn hypothesis_html(
        &self,
        hypothesis: &IdenticalHypotheses<CoqValueInfo>,
        featured: &Featured,
    ) -> Element {
        let IdenticalHypotheses(names, def, ty) = &hypothesis;
        let (featured_state, featured_in_state) = self.featured_state().unwrap();
        let mut elements: Vec<Element> = Vec::new();
        for NamesId::Id(name) in names {
            let mut featured_toggling_this = featured.clone();
            {
                let featuring_this = FeaturedInState::Hypothesis {
                    name: name.clone(),
                    subterm: None,
                };
                let f = featured_toggling_this.featured_in_current_mut();
                if *f == featuring_this {
                    *f = FeaturedInState::Nothing;
                } else {
                    *f = FeaturedInState::Hypothesis {
                        name: name.clone(),
                        subterm: None,
                    };
                }
            }
            let onclick =
                serde_json::to_string(&Input::SetFeatured(featured_toggling_this)).unwrap();

            let mut class = "hypothesis_name_wrapper not_featured";
            let mut dropdown: Option<Element> = None;
            if let FeaturedInState::Hypothesis {
                name: featured_name,
                subterm,
            } = featured_in_state
            {
                if featured_name == name {
                    class = "hypothesis_name_wrapper featured";

                    let mut menu_elements: Vec<Element> = Vec::new();
                    let mut row_id = 1;
                    for tactic_h in HYPOTHESIS_TACTICS.split_inclusive(".") {
                        let tactic = tactic_h.replace("H", name);
                        let tactic = Tactic::from_string(tactic);
                        if let Some(child) = featured_state.child(&tactic) {
                            let style = format!("grid-row: {} / span 1", row_id);
                            row_id += 1;
                            let diff = featured_state
                                .goals
                                .only_difference_in_hypothesis_html(&child.goals, name);
                            let popup_result = if diff.is_some() {
                                None
                            } else {
                                Some(html! {
                                    <div class="popup_result">{featured_state.goals.diff_html(&child.goals)}</div>
                                })
                            };
                            let onclick = featured.extended(tactic.clone()).input_string();
                            menu_elements.push(html! {
                                <div class="tactic_entry" style={&style} data-onclick={onclick}>
                                    <pre class="tactic">{text!("{}", tactic.human_string())}</pre>
                                    {popup_result}
                                </div>
                            });
                            if let Some(diff) = diff {
                                menu_elements.push(html! {
                                    <div class="inline_result" style={&style}>{diff}</div>
                                });
                            }
                        }
                    }
                    dropdown = Some(html! {
                        <div class="tactic_menu">{menu_elements}</div>
                    });
                }
            }

            elements.push(html! {
                <div class={class} data-onclick={onclick}>
                    <pre class="hypothesis_name">{text!("{}", name)}</pre>
                    {dropdown}
                </div>
            });
            elements.push(html! { <pre>{text!(", ")}</pre> });
        }
        elements.pop();

        if let Some(def) = def {
            elements.push(html! { <pre>{text!(" := {}", def.string)}</pre> });
        }

        elements.push(html! { <pre>{text!(" : {}", ty.string)}</pre> });

        html! {
            <div class="hypothesis">
                {elements}
            </div>
        }
    }
    fn conclusion_html(&self, _featured: &Featured) -> Element {
        let (featured_state, _featured_in_state) = self.featured_state().unwrap();
        html! {
            <div class="conclusion">
                <pre>{text!("{}", featured_state.goals.goals.first().unwrap().ty.string)}</pre>
            </div>
        }
    }

    fn whole_interface_html(&self) -> Element {
        let (proof_root, featured): (&ProofState, &Featured) = match &self.known_mode {
            None => return text!("Processing..."),
            Some(Mode::NotProofMode) => return text!("Not in proof mode"),
            Some(Mode::ProofMode(p, f)) => (p, f),
        };

        let featured_state = proof_root.descendant(featured.tactics_path()).unwrap();
        let attempted_tactics = self.attempted_tactics_html(featured);
        let mut prior_tactics: Vec<Element> = Vec::new();
        for (index, (tactic, _)) in featured.tactics.iter().enumerate() {
            let featured_after_this_tactic = Featured {
                num_tactics_run: index + 1,
                ..featured.clone()
            };
            let state = proof_root
                .descendant(featured_after_this_tactic.tactics_path())
                .unwrap();
            let onclick =
                serde_json::to_string(&Input::SetFeatured(featured_after_this_tactic)).unwrap();
            let class = if index + 1 < featured.num_tactics_run {
                "prior_tactic past not_present"
            } else if index + 1 == featured.num_tactics_run {
                "prior_tactic present"
            } else {
                "prior_tactic future not_present"
            };
            prior_tactics.push(html! {
                <div class={class} data-onclick={onclick}>
                    <div class="tactic">
                        <pre>{text!("{}", tactic.human_string())}</pre>
                    </div>
                    {state.goals.html()}
                </div>
            });
        }
        if !prior_tactics.is_empty() {
            prior_tactics = vec![html! {
                <div class="prior_tactics_row">
                    <h2>
                        {text!("And you've already done this stuff:")}
                    </h2>
                    <div class="prior_tactics">
                        {prior_tactics}
                    </div>
                </div>
            }]
        }

        let current_goal: Option<Element> = featured_state.goals.goals.first().map(|first_goal| {
            let conclusion = self.conclusion_html(featured);
            let result: Element = if first_goal.hyp.is_empty() {
                html! {
                    <div class="current_goal">
                        <h2>
                            {text!("Now you want to prove this:")}
                        </h2>
                        {conclusion}
                    </div>
                }
            } else {
                let hypotheses = first_goal
                    .hyp
                    .iter()
                    .map(|h| self.hypothesis_html(h, featured));
                html! {
                    <div class="current_goal">
                        <h2>
                            {text!("Now you know this stuff:")}
                        </h2>
                        {hypotheses}
                        <h2>
                            {text!("And you want to prove this:")}
                        </h2>
                        {conclusion}
                    </div>
                }
            };
            result
        });

        let onclick_root_featured = Featured {
            num_tactics_run: 0,
            ..featured.clone()
        };
        let onclick_root =
            serde_json::to_string(&Input::SetFeatured(onclick_root_featured)).unwrap();
        let proof_root_class = if featured.num_tactics_run > 0 {
            "proof_root past not_present"
        } else {
            "proof_root present"
        };

        html! {
            <div class="whole_interface">
                <div class={proof_root_class} data-onclick={onclick_root}>
                    <h2>
                        {text!("So you started with this:")}
                    </h2>
                    {proof_root.goals.html()}
                </div>
                {prior_tactics}
                <div class="main_area">
                    {current_goal}
                    {attempted_tactics}
                </div>
            </div>
        }
    }
}

#[get("/")]
fn index(rocket_state: State<RocketState>) -> Option<NamedFile> {
    NamedFile::open(rocket_state.root_path.join("static/index.html")).ok()
}

#[get("/media/<file..>")]
fn media(file: PathBuf, rocket_state: State<RocketState>) -> Option<NamedFile> {
    NamedFile::open(rocket_state.root_path.join("static/media/").join(file)).ok()
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Debug)]
pub enum Input {
    SetFeatured(Featured),
}

#[post("/input", data = "<input>")]
fn input(input: Json<Input>, rocket_state: State<RocketState>) {
    let Json(input) = input;
    let mut guard = rocket_state.application_state.lock();
    let application: &mut ApplicationState = &mut *guard;

    // assume every input might cause a UI change
    application.last_ui_change_serial_number += 1;

    match input {
        Input::SetFeatured(new_featured) => {
            // gotta check if this input wasn't delayed across a file reload
            if let Some(Mode::ProofMode(p, f)) = &mut application.known_mode {
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
    let mut guard = rocket_state.application_state.lock();
    let application: &mut ApplicationState = &mut *guard;

    if parameters.last_ui_change_serial_number == Some(application.last_ui_change_serial_number) {
        return Json(ContentResponse {
            last_ui_change_serial_number: application.last_ui_change_serial_number,
            ui_replacement: None,
        });
    }

    let whole_interface_html = application.whole_interface_html();

    let document: DOMTree<String> = html! {
        <div id="content">
            {whole_interface_html}
        </div>
    };
    let document = document.to_string();
    //eprintln!("Sending to frontend: {}", document);
    Json(ContentResponse {
        last_ui_change_serial_number: application.last_ui_change_serial_number,
        ui_replacement: Some(document),
    })
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
            "received valid input from sertop: {:?}\n{}\n",
            interpreted, line
        );

        let mut guard = application_state.lock();
        let application: &mut ApplicationState = &mut *guard;

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
                    // assume every completed command might cause a UI change
                    application.last_ui_change_serial_number += 1;
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
    // Hack: Compile the scss at the beginning of the main program.
    // This would be better as some sort of build script, but that's not a big concern right now
    // TODO: improve on that
    let mut scss_path = root_path.clone();
    scss_path.push("style.scss");
    let mut css_path = root_path.clone();
    css_path.extend(&["static", "media", "style.css"]);
    let sass_status = process::Command::new("sass")
        .args(&[scss_path, css_path])
        .status()
        .expect("error getting sass status");
    assert!(sass_status.success(), "sass failed");

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
        last_ui_change_serial_number: 0,
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
    .mount("/", routes![index, media, input, content])
    .manage(RocketState {
        application_state,
        root_path,
    })
    .launch();
}
