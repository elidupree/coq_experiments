/*

Autorun design:

The default proof exploration root is the last command from the file that successfully executes.

Before we can try commands one at a time, we must parse them; in order to parse them, we must Add all of them. Some of them may have parse errors, meaning the "Added commands" don't cover the entire file; subsequent to Adding them, some of them may fail to execute. Thus, the proof exploration root may before the last Added command.

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

use crate::global_state_types::{
    AddedFromFile, AddedSynthetic, CommandRunner, MainThreadState, MessageFromOutsideSertop,
    MessageToMainThread, Mode, ProofNode, ProofState, SertopState, SharedState, TacticResult,
};
use crate::goals_analysis::{CoqValueInfo, Goals};
use crate::serapi_protocol::{
    AddOptions, Answer, AnswerKind, Command, ConstrExpr, CoqObject, ExnInfo, Feedback,
    FeedbackContent, FormatOptions, PrettyPrint, PrintFormat, PrintOptions, QueryCommand,
    QueryOptions, StateId,
};
use crate::sertop_glue::{Interrupted, MessageFromSertop};
use crate::supervisor_thread::MessageFromSupervisor;
use crate::tactics::Tactic;
use crate::utils;
use crate::webserver_glue::MessageFromFrontend;
use guard::guard;
use std::default::default;
use std::io::Write;
use std::mem;
use std::time::{Duration, Instant};

impl CommandRunner {
    pub fn run(
        &mut self,
        command: Command,
        mut handler: impl FnMut(Answer),
    ) -> Result<(), Interrupted> {
        // If a previous command sent an interrupt JUST before the command was completed,
        // then the command might have completed, resulting in us returning Ok.
        // But we really do want to interrupt whatever comes next in that case, so
        // here we return Err immediately (as if the command was immediately interrupted
        // before it could make any progress).
        if let Ok(message) = self.receiver.try_recv() {
            match message {
                MessageToMainThread::FromOutsideSertop(message) => {
                    self.messages_from_outside_sertop_queue.push_back(message);
                }
                MessageToMainThread::FromSertop(_message) => {}
            }
        }
        if !self.messages_from_outside_sertop_queue.is_empty() {
            eprintln!("skipping a command due to previous interrupt");
            return Err(Interrupted);
        }

        let text = serde_lexpr::to_string(&command).unwrap();
        eprintln!("sending command to sertop: {}\n", text);
        writeln!(self.child_stdin, "{}", text).unwrap();
        let mut sertop_acknowledged_interrupt = false;

        while let Ok(message) = self.receiver.recv() {
            match message {
                MessageToMainThread::FromOutsideSertop(message) => {
                    self.messages_from_outside_sertop_queue.push_back(message);
                    // TODO send interrupt
                }
                MessageToMainThread::FromSertop(message) => match message {
                    MessageFromSertop::InterruptedWhileNoCommandRunning => {
                        panic!("something went wrong if we got Sys.Break when we thought a command was running");
                    }
                    MessageFromSertop::Invalid => {}
                    MessageFromSertop::Answer(answer) => {
                        if let Answer::Answer(_, AnswerKind::CoqExn(ExnInfo { str, .. })) = &answer
                        {
                            if str.trim() == "User interrupt." {
                                // rather than return Err immediately,
                                // we also want to consume the Completed
                                sertop_acknowledged_interrupt = true;
                                continue;
                            }
                        }

                        if let Answer::Answer(_, AnswerKind::Completed) = answer {
                            // assume every completed command might cause a UI change
                            self.shared.lock().last_ui_change_serial_number += 1;
                            if sertop_acknowledged_interrupt {
                                return Err(Interrupted);
                            } else {
                                return Ok(());
                            }
                        }

                        if !sertop_acknowledged_interrupt {
                            (handler)(answer);
                        }
                    }
                },
            }
        }
        panic!("looks like sertop crashed or something")
    }
}

impl MainThreadState {
    pub fn run(&mut self) {
        loop {
            if let Ok(()) = self.run_once() {
                std::thread::sleep(Duration::from_millis(10));
            }
        }
    }

    pub fn run_once(&mut self) -> Result<(), Interrupted> {
        self.handle_messages_from_outside();

        if !self.shared.lock().sertop_up_to_date_with_file {
            self.update_to_match_file()?
        }

        self.do_proof_exploration()?;

        Ok(())
    }

    pub fn handle_message_from_frontend(&mut self, message: MessageFromFrontend) {
        match message {
            MessageFromFrontend::SetFeatured(new_featured) => {
                // gotta check if this input wasn't delayed across a file reload
                if let Some(Mode::ProofMode(p, f)) = &mut self.shared.lock().known_mode {
                    if p.descendant(new_featured.tactics_path_all()).is_some() {
                        *f = new_featured;
                    }
                }
            }
        }
    }
    pub fn handle_message_from_supervisor(&mut self, message: MessageFromSupervisor) {
        match message {
            MessageFromSupervisor::ReplaceFile(code) => {
                let mut shared = self.shared.lock();
                shared.sertop_up_to_date_with_file = false;
                shared.current_file_code = code;
            }
        }
    }
    pub fn handle_message_from_outside(&mut self, message: MessageFromOutsideSertop) {
        match message {
            MessageFromOutsideSertop::FromFrontend(message) => {
                self.handle_message_from_frontend(message)
            }
            MessageFromOutsideSertop::FromSupervisor(message) => {
                self.handle_message_from_supervisor(message)
            }
        }
    }
    pub fn handle_messages_from_outside(&mut self) {
        for message in mem::take(&mut self.command_runner.messages_from_outside_sertop_queue) {
            self.handle_message_from_outside(message);
        }
        while let Ok(message) = self.command_runner.receiver.try_recv() {
            match message {
                MessageToMainThread::FromOutsideSertop(message) => {
                    self.handle_message_from_outside(message);
                }
                MessageToMainThread::FromSertop(_message) => {}
            }
        }
    }

    pub fn cancel(&mut self, canceled: Vec<StateId>) -> Result<(), Interrupted> {
        if canceled.is_empty() {
            return Ok(());
        }
        capture_fields_mut!(self.{
          sertop_state,
          shared,
          end_of_first_added_from_file_that_failed_to_execute
        });
        self.command_runner
            .run(Command::Cancel(canceled), |answer| {
                if let Answer::Answer(_, AnswerKind::Canceled(state_ids)) = answer {
                    sertop_state.added_from_file.retain(|added| {
                        state_ids.iter().all(|canceled| &added.state_id != canceled)
                    });
                    sertop_state.added_synthetic.retain(|added| {
                        state_ids.iter().all(|canceled| &added.state_id != canceled)
                    });
                    if sertop_state.added_from_file.len() < sertop_state.num_executed_from_file {
                        sertop_state.num_executed_from_file = sertop_state.added_from_file.len();
                        *end_of_first_added_from_file_that_failed_to_execute = None;
                        shared.lock().known_mode = None;
                    }
                    if sertop_state.added_synthetic.len() < sertop_state.num_executed_synthetic {
                        sertop_state.num_executed_synthetic = sertop_state.added_synthetic.len();
                    }
                }
            })
    }

    pub fn exec(&mut self, state_id: StateId) -> Result<Result<(), ExnInfo>, Interrupted> {
        let mut result = Ok(());

        self.command_runner.run(Command::Exec(state_id), |answer| {
            if let Answer::Answer(_, AnswerKind::CoqExn(exn)) = answer {
                result = Err(exn);
            }
        })?;

        Ok(result)
    }

    pub fn exec_next_from_file(&mut self) -> Result<(), Interrupted> {
        // There should never be synthetic commands while there are
        // still unexecuted ones from the file. Make sure of this.
        assert!(self.sertop_state.added_synthetic.is_empty());

        let state_id =
            self.sertop_state.added_from_file[self.sertop_state.num_executed_from_file].state_id;
        match self.exec(state_id)? {
            Ok(()) => {
                self.sertop_state.num_executed_from_file += 1;
                self.shared.lock().known_mode = None;
            }
            Err(_exn) => {
                self.end_of_first_added_from_file_that_failed_to_execute = Some(
                    self.sertop_state.added_from_file[self.sertop_state.num_executed_from_file]
                        .location_in_file
                        .end,
                );
            }
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
        capture_fields_mut!(self.sertop_state);
        self.command_runner.run(
            Command::Add(
                AddOptions {
                    ontop: last_added_id,
                    ..default()
                },
                unhandled_file_contents,
            ),
            |answer| {
                if let Answer::Answer(_, AnswerKind::Added(state_id, location, _extra)) = answer {
                    sertop_state.added_from_file.push(AddedFromFile {
                        location_in_file: unhandled_file_offset + location.bp as usize
                            ..unhandled_file_offset + location.ep as usize,
                        state_id,
                    });
                }
            },
        )
    }

    pub fn execute_from_file_until_changed_part(
        &mut self,
        first_difference_offset: Option<usize>,
    ) -> Result<(), Interrupted> {
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
        let canceled: Vec<_> = self.sertop_state.added_from_file
            [self.sertop_state.num_executed_from_file..]
            .iter()
            .map(|a| a.state_id)
            .collect();
        self.cancel(canceled)?;

        Ok(())
    }

    pub fn update_to_match_file(&mut self) -> Result<(), Interrupted> {
        let shared = self.shared.lock();
        let first_difference_offset = utils::first_difference_index(
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
        self.execute_from_file_until_changed_part(first_difference_offset)?;

        // Finally, if the file has changed, then we need to Add the remaining part,
        // UNLESS that part is after the first execution error from the file,
        // in which case we don't have to care about it yet.
        if let Some(first_difference_offset) = first_difference_offset {
            if self
                .end_of_first_added_from_file_that_failed_to_execute
                .map_or(true, |i| first_difference_offset < i)
            {
                // if we're adding new commands, this'll need to be recomputed:
                self.end_of_first_added_from_file_that_failed_to_execute = None;

                // Assume that synthetic commands must be canceled before we can even
                // attempt adding new ones from the file
                let canceled = self
                    .sertop_state
                    .added_synthetic
                    .iter()
                    .map(|a| a.state_id)
                    .collect();
                self.cancel(canceled)?;
                self.add_rest_of_file()?;
                self.execute_from_file_until_changed_part(None)?;
            }
        }

        self.shared.lock().sertop_up_to_date_with_file = true;

        Ok(())
    }

    pub fn query_goals_constr_expr(&mut self) -> Result<Option<Goals<ConstrExpr>>, Interrupted> {
        let mut received_goals = None;

        self.command_runner.run(
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
            |answer| {
                let mut objects = if let Answer::Answer(_, AnswerKind::ObjList(objects)) = answer {
                    objects
                } else {
                    return;
                };
                if let Some(CoqObject::CoqExtGoal(goals)) = objects.pop() {
                    received_goals = Some(goals)
                }
            },
        )?;

        Ok(received_goals)
    }

    pub fn print_constr_expr(
        &mut self,
        constr_expr: ConstrExpr,
    ) -> Result<Option<String>, Interrupted> {
        let mut result = None;
        self.command_runner.run(
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
            |answer| {
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
        self.command_runner.run(
            Command::Query(
                QueryOptions {
                    sid: self.sertop_state.last_added().unwrap_or(0),
                    ..default()
                },
                QueryCommand::Vernac("Show Proof. ".to_string()),
            ),
            |answer| {
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
            sertop_state: &SertopState,
            shared: &'a mut SharedState,
        ) -> &'a mut ProofNode {
            let root = match &mut shared.known_mode {
                Some(Mode::ProofMode(p, _)) => p,
                _ => panic!("shouldn't have run a tactic when not in proof mode"),
            };
            root.descendant_mut(
                sertop_state.added_synthetic[..sertop_state.num_executed_synthetic]
                    .iter()
                    .map(|t| &t.tactic),
            )
            .expect("sertop_state claims to be ahead of ProofNode tree?")
        }

        let mut exception_happened = false;
        let tactic_start_time = Instant::now();
        capture_fields_mut!(self.{sertop_state, shared});
        self.command_runner.run(
            Command::Add(
                AddOptions {
                    ontop: sertop_state.last_added(),
                    ..default()
                },
                tactic.coq_string(),
            ),
            |answer| match answer {
                Answer::Answer(_, AnswerKind::Added(state_id, _location, _extra)) => {
                    sertop_state.added_synthetic.push(AddedSynthetic {
                        tactic: tactic.clone(),
                        state_id,
                    });
                }
                Answer::Answer(_, AnswerKind::CoqExn(exn)) => {
                    exception_happened = true;
                    assert_eq!(
                        sertop_state.num_executed_synthetic,
                        sertop_state.added_synthetic.len()
                    );
                    let shared_arc = shared.clone();
                    let mut shared = shared_arc.lock();
                    let insert_result = latest_proof_node_mut(sertop_state, &mut *shared)
                        .attempted_tactics
                        .insert(tactic.clone(), TacticResult::Failure(exn));
                    assert!(
                        insert_result.is_none(),
                        "shouldn't have added a tactic that was already tested and failed (on Add)"
                    );
                }
                _ => {}
            },
        )?;

        if exception_happened {
            return Ok(());
        }

        let state_id =
            self.sertop_state.added_synthetic[self.sertop_state.num_executed_synthetic].state_id;
        let exec_result = self.exec(state_id)?;
        if let Err(exn) = exec_result {
            let shared_arc = self.shared.clone();
            let mut shared = shared_arc.lock();
            assert_eq!(
                self.sertop_state.num_executed_synthetic + 1,
                self.sertop_state.added_synthetic.len()
            );
            let insert_result = latest_proof_node_mut(&self.sertop_state, &mut *shared)
                .attempted_tactics
                .insert(tactic, TacticResult::Failure(exn));
            assert_eq!(
                insert_result, None,
                "shouldn't have added a tactic that was already tested and failed (on Exec)"
            );

            return Ok(());
        }

        let tactic_duration = Instant::now() - tactic_start_time;

        // If we haven't tried this tactic before, create a proof note for it.
        // Unfortunately we have to do the whole lookup twice, because we don't
        // want to run self.query_proof_state() if it doesn't already exist,
        // but we can't hold the reference across the query call because it's
        // inside the Mutex.
        let shared_arc = self.shared.clone();
        if latest_proof_node_mut(&self.sertop_state, &mut *shared_arc.lock())
            .attempted_tactics
            .get(&tactic)
            .is_none()
        {
            // if query_proof_state gets interrupted, we still want to
            // increment num_executed_synthetic, so don't use ?:
            match self.query_proof_state() {
                Ok(new_state) => {
                    latest_proof_node_mut(&self.sertop_state, &mut *shared_arc.lock()).attempted_tactics.insert(
                        tactic,
                        TacticResult::Success {
                            duration: tactic_duration,
                            result_node: ProofNode::new(new_state.expect(
                                "after a successful tactic, we should be able to get a proof state",
                            )),
                        },
                    );
                }
                Err(Interrupted) => {
                    self.sertop_state.num_executed_synthetic += 1;
                    return Err(Interrupted);
                }
            }
        }
        self.sertop_state.num_executed_synthetic += 1;

        // basically an assertion that the node exists, one way or another:
        latest_proof_node_mut(&self.sertop_state, &mut *shared_arc.lock());

        Ok(())
    }
}
