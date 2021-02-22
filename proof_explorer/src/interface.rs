#![allow(unused_imports, clippy::collapsible_else_if)]

use derivative::Derivative;
use difference::{Changeset, Difference};
use guard::guard;
use parking_lot::{Mutex, MutexGuard};
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
use std::time::{Duration, Instant, SystemTime};
use std::{fs, iter, mem};
use typed_html::dom::DOMTree;
use typed_html::elements::FlowContent;
use typed_html::{html, text};
//use rocket::response::content::Json;

use crate::global_state_types::{
    AddedFromFile, AddedSynthetic, Featured, FeaturedInNode, Mode, ProofNode, ProofState,
    RocketState, SertopState, SertopThreadState, SharedState, TacticResult,
};
use crate::goals_analysis::{CoqValueInfo, Goals};
use crate::serapi_protocol::{
    AddOptions, Answer, AnswerKind, Command, ConstrExpr, CoqObject, ExnInfo, Feedback,
    FeedbackContent, FormatOptions, IdenticalHypotheses, NamesId, PrettyPrint, PrintFormat,
    PrintOptions, QueryCommand, QueryOptions, ReifiedGoal, SerGoals, StateId,
};
use crate::tactics::{self, Tactic};
use crate::utils::first_difference_index;
use crate::webserver_glue;
use rocket_contrib::serve::StaticFiles;

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

impl SharedState {
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
                self.sertop_up_to_date_with_file = false;
            }
        }
    }
}

impl SharedState {
    fn tactic_menu_html(&self, tactics: impl IntoIterator<Item = Tactic>) -> Element {
        guard!(let Some(Mode::ProofMode(_proof_root, featured)) = &self.known_mode else {unreachable!()});
        let (featured_node, _) = self.featured_node().unwrap();
        let entries = tactics.into_iter().map(|tactic| {
            guard!(let Some(TacticResult::Success { duration, result_node })
                = featured_node.attempted_tactics.get(&tactic) else {panic!("tactic_menu_html doesn't support entries for failing tactics yet")});
            let name = tactic.human_string();
            let onclick = featured.extended(tactic).input_string();

            let duration: Option<Element> = if duration > &Duration::from_millis(50) {
                Some(html! {
                    <div class="duration">
                        {text!("Took {}ms", duration.as_millis())}
                    </div>
                })
            } else {
                None
            };
            html! {
                <div class="tactic_entry" data-onclick={onclick}>
                    <pre class="tactic">{text!("{}", name)}</pre>
                    <div class="popup_result">
                        {duration}
                        {featured_node.state.goals.diff_html(&result_node.state.goals)}
                    </div>
                </div>
            }
        });
        html! {
            <div class="tactic_menu">{entries}</div>
        }
    }

    fn attempted_tactics_html(&self) -> Vec<Element> {
        let (featured_node, _) = self.featured_node().unwrap();
        let first_goal = match featured_node.state.goals.goals.first() {
            Some(goal) => goal,
            None => {
                return vec![text!(
                "All goals solved! (Except maybe shelved goals, I haven't implemented that yet)."
            )]
            }
        };

        let mut solvers: Vec<_> =
            tactics::generate_exploratory_tactics(featured_node, &FeaturedInNode::Nothing)
                .into_iter()
                .filter(|tactic| !tactic.useless(featured_node))
                .filter(|tactic| {
                    featured_node
                        .child(tactic)
                        .expect("unsuccessful tactics should've been useless")
                        .state
                        .goals
                        .goals
                        .len()
                        < featured_node.state.goals.goals.len()
                })
                .collect();
        let mut results: Vec<Element> = Vec::new();
        let solved = !solvers.is_empty();
        if solved {
            fn proof_length_fn(featured_node: &ProofNode, tactic: &Tactic) -> usize {
                featured_node
                    .child(tactic)
                    .unwrap()
                    .state
                    .proof_string
                    .as_ref()
                    .map_or(1 << 30, String::len)
            }
            solvers.sort_by_key(|t| (proof_length_fn)(featured_node, t));
            let best_size = (proof_length_fn)(featured_node, &solvers[0]);
            let (best_solvers, worse_solvers): (Vec<_>, Vec<_>) = solvers
                .into_iter()
                .partition(|tactic| (proof_length_fn)(featured_node, tactic) == best_size);
            let best_solvers = self.tactic_menu_html(best_solvers);
            let worse_solvers: Vec<Element> = if worse_solvers.is_empty() {
                Vec::new()
            } else {
                vec![
                    html! {
                        <h3>
                            {text!("These also solve it, but they make larger proofs:")}
                        </h3>
                    },
                    self.tactic_menu_html(worse_solvers),
                ]
            };
            results.push(html! {
                <div class="solvers">
                    <h2>
                        {text!("This goal is immediately solved by:")}
                    </h2>
                    {best_solvers}
                    {worse_solvers}
                </div>
            })
        }

        let global_tactics = self.tactic_menu_html(
            tactics::all_global_tactics()
                .filter(|tactic| !tactic.useless(featured_node))
                .filter(|tactic| {
                    featured_node
                        .child(tactic)
                        .expect("unsuccessful tactics should've been useless")
                        .state
                        .goals
                        .goals
                        .len()
                        >= featured_node.state.goals.goals.len()
                }),
        );
        let hyp_note = if first_goal.hyp.is_empty() {
            None
        } else {
            Some(html! {
                <div class="click_hypotheses_note">
                    {text!("(Or click one of the hypothesis names to the left, to see tactics related to that hypothesis.)")}
                </div>
            })
        };
        if solved {
            results.push(html! {
                <div class="global_tactics">
                    <h2 class="deemphasize">
                        {text!("(These don't solve it:)")}
                    </h2>
                    {global_tactics}
                    {hyp_note}
                </div>
            });
        } else {
            results.push(html! {
                <div class="global_tactics">
                    <h2>
                        {text!("Try one of these tactics:")}
                    </h2>
                    {global_tactics}
                    {hyp_note}
                </div>
            });
        }

        results
    }
    fn hypothesis_html(
        &self,
        hypothesis: &IdenticalHypotheses<CoqValueInfo>,
        featured: &Featured,
    ) -> Element {
        let IdenticalHypotheses(names, def, ty) = &hypothesis;
        let (featured_node, featured_in_node) = self.featured_node().unwrap();
        let mut elements: Vec<Element> = Vec::new();
        for NamesId::Id(name) in names {
            let mut featured_toggling_this = featured.clone();
            {
                let featuring_this = FeaturedInNode::Hypothesis {
                    name: name.clone(),
                    subterm: None,
                };
                let f = featured_toggling_this.featured_in_current_mut();
                if *f == featuring_this {
                    *f = FeaturedInNode::Nothing;
                } else {
                    *f = FeaturedInNode::Hypothesis {
                        name: name.clone(),
                        subterm: None,
                    };
                }
            }
            let onclick = featured_toggling_this.input_string();

            let mut class = "hypothesis_name_wrapper not_featured";
            let mut dropdown: Option<Element> = None;
            if let FeaturedInNode::Hypothesis {
                name: featured_name,
                subterm,
            } = featured_in_node
            {
                if featured_name == name {
                    class = "hypothesis_name_wrapper featured";

                    dropdown = Some(
                        self.tactic_menu_html(
                            tactics::hypothesis_tactics(name)
                                .filter(|tactic| !tactic.useless(featured_node)),
                        ),
                    );
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
        let (featured_node, _featured_in_node) = self.featured_node().unwrap();
        html! {
            <div class="conclusion">
                <pre>{text!("{}", featured_node.state.goals.goals.first().unwrap().ty.string)}</pre>
            </div>
        }
    }

    pub fn whole_interface_html(&self) -> Element {
        let (proof_root, featured): (&ProofNode, &Featured) = match &self.known_mode {
            None => return text!("Processing..."),
            Some(Mode::NotProofMode) => return text!("Not in proof mode"),
            Some(Mode::ProofMode(p, f)) => (p, f),
        };

        let featured_node = proof_root.descendant(featured.tactics_path()).unwrap();
        let attempted_tactics = self.attempted_tactics_html();
        let mut prior_tactics: Vec<Element> = Vec::new();
        for (index, (tactic, _)) in featured.tactics.iter().enumerate() {
            let featured_after_this_tactic = Featured {
                num_tactics_run: index + 1,
                ..featured.clone()
            };
            let node = proof_root
                .descendant(featured_after_this_tactic.tactics_path())
                .unwrap();
            let onclick = featured_after_this_tactic.input_string();
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
                    {node.state.goals.html()}
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

        let current_goal: Option<Element> =
            featured_node.state.goals.goals.first().map(|first_goal| {
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
        let onclick_root = onclick_root_featured.input_string();
        let proof_root_class = if featured.num_tactics_run > 0 {
            "proof_root past not_present"
        } else {
            "proof_root present"
        };

        let mut featured_deselecting = featured.clone();
        *featured_deselecting.featured_in_current_mut() = FeaturedInNode::Nothing;
        let onclick_default = featured_deselecting.input_string();

        html! {
            <div class="whole_interface" data-onclick={onclick_default}>
                <div class={proof_root_class} data-onclick={onclick_root}>
                    <h2>
                        {text!("So you started with this:")}
                    </h2>
                    {proof_root.state.goals.html()}
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

pub struct Interrupted;
#[allow(clippy::large_enum_variant)] // it's expected that it will *usually* be the large variant
pub enum AnswersStreamItem {
    InterruptedWhileNoCommandRunning,
    Invalid,
    Answer(Answer),
}

pub fn interpret_sertop_line(line: String) -> AnswersStreamItem {
    // note that there are to different ways sertop response to interrupts:
    // Sys.Break if there is no command running;
    // (Answer N(CoqExn ... str"\nUser interrupt")))) if there is a command running.
    if line.trim() == "Sys.Break" {
        return AnswersStreamItem::InterruptedWhileNoCommandRunning;
    }
    let parsed = serde_lexpr::parse::from_str(&line);
    let parsed = match parsed {
        Ok(parsed) => parsed,
        Err(err) => {
            eprintln!(
                "received invalid S-expression from sertop ({:?}):\n{}\n",
                err, line
            );
            return AnswersStreamItem::Invalid;
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
            return AnswersStreamItem::Invalid;
        }
    };
    eprintln!(
        "received valid input from sertop: {:?}\n{}\n",
        interpreted, line
    );
    AnswersStreamItem::Answer(interpreted)
}

impl SertopThreadState {
    pub fn run_command(
        &mut self,
        command: Command,
        mut handler: impl FnMut(Answer, &mut SertopThreadState, &mut SharedState),
    ) -> Result<(), Interrupted> {
        let text = serde_lexpr::to_string(&command).unwrap();
        eprintln!("sending command to sertop: {}\n", text);
        writeln!(self.child_stdin, "{}", text).unwrap();
        let mut interrupted = false;

        while let Some(line) = self.lines_iterator.next() {
            let line = line.expect("IO error receiving from sertop?");
            match interpret_sertop_line(line) {
                AnswersStreamItem::InterruptedWhileNoCommandRunning => {
                    panic!("something went wrong if we got Sys.Break when we thought a command was running");
                }
                AnswersStreamItem::Invalid => {}
                AnswersStreamItem::Answer(answer) => {
                    if let Answer::Answer(_, AnswerKind::CoqExn(ExnInfo { str, .. })) = &answer {
                        if str.trim() == "User interrupt." {
                            // rather than return Err immediately,
                            // we also want to consume the Completed
                            interrupted = true;
                            continue;
                        }
                    }

                    let shared_arc = self.shared.clone();
                    let mut shared = shared_arc.lock();

                    if let Answer::Answer(_, AnswerKind::Completed) = answer {
                        // assume every completed command might cause a UI change
                        shared.last_ui_change_serial_number += 1;
                        if interrupted {
                            return Err(Interrupted);
                        } else {
                            return Ok(());
                        }
                    }

                    if !interrupted {
                        (handler)(answer, self, &mut *shared);
                    }
                }
            }
        }
        panic!("looks like sertop crashed or something")
    }

    pub fn cancel(&mut self, canceled: Vec<StateId>) -> Result<(), Interrupted> {
        self.run_command(
            Command::Cancel(canceled),
            |answer, sertop_thread, shared| {
                if let Answer::Answer(_, AnswerKind::Canceled(state_ids)) = answer {
                    sertop_thread.sertop_state.added_from_file.retain(|added| {
                        state_ids.iter().all(|canceled| &added.state_id != canceled)
                    });
                    sertop_thread.sertop_state.added_synthetic.retain(|added| {
                        state_ids.iter().all(|canceled| &added.state_id != canceled)
                    });
                    if sertop_thread.sertop_state.added_from_file.len()
                        < sertop_thread.sertop_state.num_executed_from_file
                    {
                        sertop_thread.sertop_state.num_executed_from_file =
                            sertop_thread.sertop_state.added_from_file.len();
                        sertop_thread.end_of_first_added_from_file_that_failed_to_execute = None;
                        shared.known_mode = None;
                    }
                    if sertop_thread.sertop_state.added_synthetic.len()
                        < sertop_thread.sertop_state.num_executed_synthetic
                    {
                        sertop_thread.sertop_state.num_executed_synthetic =
                            sertop_thread.sertop_state.added_synthetic.len();
                    }
                }
            },
        )
    }

    pub fn exec_next_from_file(&mut self) -> Result<(), Interrupted> {
        // There should never be synthetic commands while there are
        // still unexecuted ones from the file. Make sure of this.
        assert!(self.sertop_state.added_synthetic.is_empty());

        self.run_command(
            Command::Exec(
                self.sertop_state.added_from_file[self.sertop_state.num_executed_from_file]
                    .state_id,
            ),
            |answer, sertop_thread, _shared| {
                if let Answer::Answer(_, AnswerKind::CoqExn(_)) = answer {
                    sertop_thread.end_of_first_added_from_file_that_failed_to_execute = Some(
                        sertop_thread.sertop_state.added_from_file
                            [sertop_thread.sertop_state.num_executed_from_file]
                            .location_in_file
                            .end,
                    );
                }
            },
        )?;

        let mut shared = self.shared.lock();
        if self
            .end_of_first_added_from_file_that_failed_to_execute
            .is_none()
        {
            self.sertop_state.num_executed_from_file += 1;
            shared.known_mode = None;
        }
        Ok(())
    }

    pub fn add_rest_of_file(&mut self) -> Result<(), Interrupted> {
        let shared = self.shared.lock();
        let (unhandled_file_offset, last_added_id) = self
            .sertop_state
            .added_from_file
            .last()
            .map_or((0, None), |a| (a.location_in_file.end, Some(a.state_id)));
        let unhandled_file_contents = shared.current_file_code[unhandled_file_offset..].to_owned();
        self.last_added_file_code = shared.current_file_code.clone();

        drop(shared);
        self.run_command(
            Command::Add(
                AddOptions {
                    ontop: last_added_id,
                    ..default()
                },
                unhandled_file_contents,
            ),
            |answer, sertop_thread, _shared| {
                if let Answer::Answer(_, AnswerKind::Added(state_id, location, _extra)) = answer {
                    sertop_thread
                        .sertop_state
                        .added_from_file
                        .push(AddedFromFile {
                            location_in_file: unhandled_file_offset + location.bp as usize
                                ..unhandled_file_offset + location.ep as usize,
                            state_id,
                        });
                }
            },
        )
    }

    pub fn update_to_match_file(&mut self) -> Result<(), Interrupted> {
        let shared = self.shared.lock();
        let first_difference_offset = first_difference_index(
            shared.current_file_code.as_bytes(),
            self.last_added_file_code.as_bytes(),
        );
        drop(shared);

        // First, if a file change has invalidated any commands that were
        // actually executed, cancel them.
        if let Some(first_difference_offset) = first_difference_offset {
            let need_to_cancel = self.sertop_state.added_from_file
                [..self.sertop_state.num_executed_from_file]
                .last()
                .map_or(false, |a| a.location_in_file.end > first_difference_offset);
            if need_to_cancel {
                // In this case, it's possible that there are also synthetic commands left,
                // which we'd need to clean up.
                let canceled = self
                    .sertop_state
                    .added_from_file
                    .iter()
                    .filter(|a| a.location_in_file.end > first_difference_offset)
                    .map(|a| a.state_id)
                    .chain(self.sertop_state.added_synthetic.iter().map(|a| a.state_id))
                    .collect();

                self.cancel(canceled)?;
            }
        }

        // Otherwise, execute anything we've already added, as long as it's still
        // consistent with the file and hasn't already hit an execution error.
        while let Some(next) = self
            .sertop_state
            .added_from_file
            .get(self.sertop_state.num_executed_from_file)
        {
            if self
                .end_of_first_added_from_file_that_failed_to_execute
                .is_none()
                && first_difference_offset.map_or(true, |i| next.location_in_file.end <= i)
            {
                self.exec_next_from_file()?;
            } else {
                break;
            }
        }

        // After the above, if there are any unexecuted commands from the file, cancel them.
        // (Since they either threw errors or are inconsistent with the current file.)
        if let Some(first_difference_offset) = first_difference_offset {
            let canceled: Vec<_> = self.sertop_state.added_from_file
                [self.sertop_state.num_executed_from_file..]
                .iter()
                .map(|a| a.state_id)
                .collect();
            if !canceled.is_empty() {
                // There should never be synthetic commands while there are
                // still unexecuted ones from the file. Make sure of this.
                assert!(self.sertop_state.added_synthetic.is_empty());

                self.cancel(canceled)?;
            }

            // Finally, if the file has changed, then we need to Add the remaining part,
            // UNLESS that part is after the first execution error from the file,
            // in which case we don't have to care about it yet.
            if self
                .end_of_first_added_from_file_that_failed_to_execute
                .map_or(true, |i| first_difference_offset < i)
            {
                self.add_rest_of_file()?;
                // hack: go back and execute
                return Ok(());
            }
        }

        self.shared.lock().sertop_up_to_date_with_file = true;

        Ok(())
    }

    pub fn query_goals_constr_expr(&mut self) -> Result<Option<Goals<ConstrExpr>>, Interrupted> {
        let mut received_goals = None;

        self.run_command(
            Command::Query(
                QueryOptions {
                    sid: self.sertop_state.last_added().unwrap_or(0),
                    pp: FormatOptions {
                        pp_format: PrintFormat::PpSer,
                        ..default()
                    },
                    ..default()
                },
                QueryCommand::EGoals,
            ),
            |answer, _sertop_thread, shared| {
                let mut objects = if let Answer::Answer(_, AnswerKind::ObjList(objects)) = answer {
                    objects
                } else {
                    return;
                };
                match objects.pop() {
                    Some(CoqObject::CoqExtGoal(goals)) => received_goals = Some(goals),
                    _ => match shared.known_mode {
                        None => {
                            shared.known_mode = Some(Mode::NotProofMode);
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
            },
        )?;

        Ok(received_goals)
    }

    pub fn print_constr_expr(
        &mut self,
        constr_expr: ConstrExpr,
    ) -> Result<Option<String>, Interrupted> {
        let mut result = None;
        self.run_command(
            Command::Print(
                PrintOptions {
                    sid: self.sertop_state.last_added().unwrap_or(0),
                    pp: FormatOptions {
                        pp_format: PrintFormat::PpStr,
                        pp_margin: 9999999,
                        ..default()
                    },
                },
                CoqObject::CoqExpr(constr_expr),
            ),
            |answer, _sertop_thread, _shared| {
                let mut objects = if let Answer::Answer(_, AnswerKind::ObjList(objects)) = answer {
                    objects
                } else {
                    return;
                };
                if let Some(CoqObject::CoqString(string)) = objects.pop() {
                    result = Some(string);
                } else {
                    panic!("unexpected response to Print");
                };
            },
        )?;
        Ok(result)
    }

    pub fn query_goals_coqvalueinfo(&mut self) -> Result<Option<Goals<CoqValueInfo>>, Interrupted> {
        self.query_goals_constr_expr()?
            .map(|goals| {
                goals.map_values(|constr_expr| {
                    let string = self
                        .print_constr_expr(constr_expr.clone())?
                        .expect("didn't receive printed representation for ConstrExpr from goal");
                    Ok(CoqValueInfo {
                        string,
                        constr_expr,
                    })
                })
            })
            .transpose()
    }

    pub fn show_proof(&mut self) -> Result<Option<(PrettyPrint, String)>, Interrupted> {
        let mut result = None;
        self.run_command(
            Command::Query(
                QueryOptions {
                    sid: self.sertop_state.last_added().unwrap_or(0),
                    ..default()
                },
                QueryCommand::Vernac("Show Proof. ".to_string()),
            ),
            |answer, _sertop_thread, _shared| {
                if let Answer::Feedback(Feedback {
                    contents: FeedbackContent::Message { pp, str, .. },
                    ..
                }) = answer
                {
                    result = Some((pp, str));
                };
            },
        )?;
        Ok(result)
    }

    pub fn query_proof_state(&mut self) -> Result<Option<ProofState>, Interrupted> {
        guard!(let Some(goals) = self.query_goals_coqvalueinfo()? else {return Ok(None)});
        let proof_string = self.show_proof()?.map(|(_p, s)| s);
        Ok(Some(ProofState {
            goals,
            proof_string,
        }))
    }

    pub fn run_tactic(&mut self, tactic: Tactic) -> Result<(), Interrupted> {
        fn latest_proof_node_mut<'a>(
            sertop_thread: &mut SertopThreadState,
            shared: &'a mut SharedState,
        ) -> Option<&'a mut ProofNode> {
            let root = match &mut shared.known_mode {
                Some(Mode::ProofMode(p, _)) => p,
                _ => return None,
            };
            root.descendant_mut(
                sertop_thread.sertop_state.added_synthetic
                    [..sertop_thread.sertop_state.num_executed_synthetic]
                    .iter()
                    .map(|t| &t.tactic),
            )
        }

        let mut exception_happened = false;
        let tactic_start_time = Instant::now();
        self.run_command(
            Command::Add(
                AddOptions {
                    ontop: self.sertop_state.last_added(),
                    ..default()
                },
                tactic.coq_string(),
            ),
            |answer, sertop_thread, shared| match answer {
                Answer::Answer(_, AnswerKind::Added(state_id, _location, _extra)) => {
                    sertop_thread
                        .sertop_state
                        .added_synthetic
                        .push(AddedSynthetic {
                            tactic: tactic.clone(),
                            state_id,
                        });
                }
                Answer::Answer(_, AnswerKind::CoqExn(exn)) => {
                    exception_happened = true;
                    assert_eq!(
                        sertop_thread.sertop_state.num_executed_synthetic,
                        sertop_thread.sertop_state.added_synthetic.len()
                    );
                    let insert_result = latest_proof_node_mut(sertop_thread, shared)
                        .unwrap()
                        .attempted_tactics
                        .insert(tactic.clone(), TacticResult::Failure(exn));
                    assert!(
                        insert_result.is_none(),
                        "shouldn't have added a tactic that was already tested and failed"
                    );
                }
                _ => {}
            },
        )?;

        if exception_happened {
            return Ok(());
        }
        self.run_command(
            Command::Exec(
                self.sertop_state.added_synthetic[self.sertop_state.num_executed_synthetic]
                    .state_id,
            ),
            |answer, sertop_thread, shared| {
                if let Answer::Answer(_, AnswerKind::CoqExn(exn)) = answer {
                    exception_happened = true;
                    assert_eq!(
                        sertop_thread.sertop_state.num_executed_synthetic + 1,
                        sertop_thread.sertop_state.added_synthetic.len()
                    );
                    let insert_result = latest_proof_node_mut(sertop_thread, shared)
                        .unwrap()
                        .attempted_tactics
                        .insert(tactic.clone(), TacticResult::Failure(exn));
                    assert!(
                        insert_result.is_none(),
                        "shouldn't have queried goals for a tactic that was already tested"
                    );
                }
            },
        )?;
        if exception_happened {
            return Ok(());
        }
        let tactic_duration = Instant::now() - tactic_start_time;

        self.sertop_state.num_executed_synthetic += 1;
        let shared_arc = self.shared.clone();
        if latest_proof_node_mut(self, &mut *shared_arc.lock()).is_none() {
            if let Some(state) = self.query_proof_state()? {
                let new_proof_node = ProofNode {
                    state,
                    attempted_tactics: HashMap::new(),
                };
                let mut shared = shared_arc.lock();
                match &mut shared.known_mode {
                    None => {
                        shared.known_mode = Some(Mode::ProofMode(new_proof_node, Featured::default()));
                    }
                    Some(Mode::NotProofMode) => {
                        panic!("shouldn't have even gotten to entering a proof node when known not to be in proof mode")
                    }
                    Some(Mode::ProofMode(p,_)) => {
                        assert_eq!(self.sertop_state.num_executed_synthetic, self.sertop_state.added_synthetic.len());
                        // Note: can't use latest_proof_node_mut() here because the shared would believe we have already gotten to this spot
                        let tactics : &[AddedSynthetic] = &self.sertop_state.added_synthetic;
                        let p2 = p.descendant_mut (tactics [..tactics.len()-1].iter().map(|t|&t.tactic)).unwrap();
                        let insert_result = p2.attempted_tactics.insert(tactic,TacticResult::Success{duration: tactic_duration, result_node: new_proof_node});
                        assert!(insert_result.is_none(), "shouldn't have queried goals for a tactic that was already tested");
                    }
                }
            }
        }

        Ok(())
    }

    fn do_proof_exploration(&mut self) -> Result<(), Interrupted> {
        let shared_arc = self.shared.clone();
        if shared_arc.lock().known_mode.is_none() {
            let new_mode = Some(if let Some(state) = self.query_proof_state()? {
                let new_proof_node = ProofNode {
                    state,
                    attempted_tactics: HashMap::new(),
                };

                Mode::ProofMode(new_proof_node, Featured::default())
            } else {
                Mode::NotProofMode
            });
            shared_arc.lock().known_mode = new_mode;
        }
        let shared = shared_arc.lock();
        let (_proof_root, featured): (&ProofNode, &Featured) = match &shared.known_mode {
            None => unreachable!(),
            Some(Mode::NotProofMode) => return Ok(()),
            Some(Mode::ProofMode(p, f)) => (p, f),
        };
        let tactics_path: Vec<_> = featured.tactics_path().cloned().collect();

        // make sure we are currently at the featured proof path before exploring
        let canceled: Vec<_> = self
            .sertop_state
            .added_synthetic
            .iter()
            .enumerate()
            .skip_while(|(i, a)| tactics_path.get(*i) == Some(&a.tactic))
            .map(|(_, a)| a.state_id)
            .collect();
        drop(shared);

        if !canceled.is_empty() {
            self.cancel(canceled)?;
        }
        for catchup_tactic in &tactics_path[self.sertop_state.added_synthetic.len()..] {
            self.run_tactic(catchup_tactic.to_owned())?;
        }

        let shared = shared_arc.lock();
        let (featured_node, featured_in_node): (&ProofNode, &FeaturedInNode) =
            shared.featured_node().unwrap();
        let exploratory_tactics =
            tactics::generate_exploratory_tactics(featured_node, featured_in_node);
        drop(shared);
        for tactic in exploratory_tactics {
            let shared = shared_arc.lock();
            let (featured_node, _featured_in_node): (&ProofNode, &FeaturedInNode) =
                shared.featured_node().unwrap();
            if featured_node.attempted_tactics.get(&tactic).is_none() {
                drop(shared);
                self.run_tactic(tactic)?;
                // TODO: don't be inefficient, keep going unless featured was actually change
                // or something like that
                return Ok(());
            }
        }

        Ok(())
    }

    pub fn run_once(&mut self) -> Result<(), Interrupted> {
        while !self.shared.lock().sertop_up_to_date_with_file {
            self.update_to_match_file()?
        }

        self.do_proof_exploration()?;

        Ok(())
    }

    pub fn run(&mut self) {
        loop {
            if let Ok(()) = self.run_once() {
                std::thread::sleep(Duration::from_millis(10));
            }
        }
    }
}

pub fn processing_thread(shared: Arc<Mutex<SharedState>>) {
    loop {
        let mut guard = shared.lock();
        guard.frequent_update();
        std::mem::drop(guard);
        std::thread::sleep(Duration::from_millis(10));
    }
}

pub fn run(code_path: PathBuf) {
    // Hack: Compile the scss at the beginning of the main program.
    // This would be better as some sort of build script, but that's not a big concern right now
    // TODO: improve on that
    let scss_path = "./style.scss";
    let css_path = "./static/media/style.css";
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

    let shared = Arc::new(Mutex::new(SharedState::new(code_path)));

    std::thread::spawn({
        let mut sertop_thread = SertopThreadState {
            lines_iterator: BufReader::new(child_stdout).lines(),
            child_stdin,
            sertop_state: default(),
            shared: shared.clone(),
            last_added_file_code: String::new(),
            end_of_first_added_from_file_that_failed_to_execute: None,
        };
        move || {
            sertop_thread.run();
        }
    });

    std::thread::spawn({
        let shared = shared.clone();
        move || {
            processing_thread(shared);
        }
    });

    webserver_glue::launch(shared);
}
