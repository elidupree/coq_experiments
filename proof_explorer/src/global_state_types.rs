use crate::goals_analysis::{CoqValueInfo, Goals};
use crate::serapi_protocol::{ExnInfo, StateId};
use crate::tactics::Tactic;
use derivative::Derivative;
use guard::guard;
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::io::BufReader;
use std::iter;
use std::ops::Range;
use std::path::PathBuf;
use std::process::{ChildStdin, ChildStdout};
use std::sync::Arc;
use std::time::{Duration, SystemTime};

////////////////////////////////////////////////////////////////
// The big global piles (one shared, one for each thread ish) //
////////////////////////////////////////////////////////////////

pub struct SharedState {
    pub code_path: PathBuf,
    pub current_file_code: String,
    pub sertop_up_to_date_with_file: bool,
    // TODO : this isn't the most efficient file watcher system, figure out what is?
    pub last_code_modified: Option<SystemTime>,

    pub known_mode: Option<Mode>,

    pub last_ui_change_serial_number: u64,
}

pub struct RocketState {
    pub shared: Arc<Mutex<SharedState>>,
}

pub struct SertopThreadState {
    pub command_runner: CommandRunner,
    pub sertop_state: SertopState,
    pub shared: Arc<Mutex<SharedState>>,
    pub last_added_file_code: String,
    pub end_of_first_added_from_file_that_failed_to_execute: Option<usize>,
}

/// A sub-struct of SertopThreadState, responsible for raw IO with sertop.
/// Wants to be a separate substruct so you can take an &mut CommandRunner
/// without hogging up &mut references to the rest of SertopThreadState.
pub struct CommandRunner {
    pub child_stdin: ChildStdin,
    pub lines_iterator: std::io::Lines<BufReader<ChildStdout>>,
    // why a duplicate pointer to SharedState, you ask?
    // again, it's about reference lifetimes. Before I separated out CommandRunner,
    // I had to make a copy of the Arc on the stack; having it here is no worse
    pub shared: Arc<Mutex<SharedState>>,
}

impl SharedState {
    pub fn new(code_path: PathBuf) -> Self {
        SharedState {
            code_path,
            current_file_code: String::new(),
            sertop_up_to_date_with_file: false, // maybe theoretically it's already up to date with the null file, but there's no need to be clever
            last_code_modified: None,
            known_mode: None,
            last_ui_change_serial_number: 0,
        }
    }

    pub fn featured_node(&self) -> Option<(&ProofNode, &FeaturedInNode)> {
        guard!(let Some(Mode::ProofMode(proof_root, featured)) = &self.known_mode else {return None});
        Some((
            proof_root.descendant(featured.tactics_path()).unwrap(),
            featured.featured_in_current(),
        ))
    }
}

///////////////////////////////////////////////////////////////////
// Stuff to remember about the state of the sertop child process //
///////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub struct AddedFromFile {
    pub location_in_file: Range<usize>,
    pub state_id: StateId,
}

#[derive(Debug)]
pub struct AddedSynthetic {
    pub tactic: Tactic,
    pub state_id: StateId,
}

#[derive(Debug, Default)]
pub struct SertopState {
    pub added_from_file: Vec<AddedFromFile>,
    pub added_synthetic: Vec<AddedSynthetic>,
    pub num_executed_from_file: usize,
    pub num_executed_synthetic: usize,
}

impl SertopState {
    pub fn last_added(&self) -> Option<StateId> {
        self.added_synthetic
            .last()
            .map(|a| a.state_id)
            .or_else(|| self.added_from_file.last().map(|a| a.state_id))
    }
}

///////////////////////////////////////////////////////////////////
//    The tree of tactics we've explored (part of SharedState)   //
///////////////////////////////////////////////////////////////////

#[derive(PartialEq, Eq, Debug)]
pub enum Mode {
    ProofMode(ProofNode, Featured),
    NotProofMode,
}

#[derive(PartialEq, Eq, Debug)]
pub struct ProofNode {
    pub state: ProofState,
    pub attempted_tactics: HashMap<Tactic, TacticResult>,
}

#[derive(PartialEq, Eq, Debug)]
pub struct ProofState {
    pub goals: Goals<CoqValueInfo>,
    // This doesn't really want to be an Option; None is here to represent the case where
    // serde_lexpr hit its hard-coded recursion limit and couldn't parse the Pp
    // that sertop sends along with the string
    pub proof_string: Option<String>,
}

#[derive(PartialEq, Eq, Debug)]
pub enum TacticResult {
    Success {
        duration: Duration,
        result_node: ProofNode,
    },
    Timeout(Duration),
    Failure(ExnInfo),
}

impl ProofNode {
    pub fn child(&self, tactic: &Tactic) -> Option<&ProofNode> {
        match self.attempted_tactics.get(tactic) {
            Some(TacticResult::Success { result_node, .. }) => Some(result_node),
            _ => None,
        }
    }
    pub fn child_mut(&mut self, tactic: &Tactic) -> Option<&mut ProofNode> {
        match self.attempted_tactics.get_mut(tactic) {
            Some(TacticResult::Success { result_node, .. }) => Some(result_node),
            _ => None,
        }
    }
    pub fn descendant<'a>(
        &self,
        mut tactics: impl Iterator<Item = &'a Tactic>,
    ) -> Option<&ProofNode> {
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
    ) -> Option<&mut ProofNode> {
        match tactics.next() {
            None => Some(self),
            Some(tactic) => self
                .child_mut(tactic)
                .and_then(|child| child.descendant_mut(tactics)),
        }
    }
}

//////////////////////////////////////////////////////////////////
//     Types for UI state that is controlled by the user        //
// (part of SharedState because it influences where to explore) //
//////////////////////////////////////////////////////////////////

#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize, Derivative)]
#[derivative(Default)]
pub enum FeaturedInNode {
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
    pub featured_in_root: FeaturedInNode,
    pub tactics: Vec<(Tactic, FeaturedInNode)>,
    pub num_tactics_run: usize,
}

impl Featured {
    pub fn tactics_path(&self) -> impl Iterator<Item = &Tactic> {
        self.tactics_path_all().take(self.num_tactics_run)
    }
    pub fn tactics_path_all(&self) -> impl Iterator<Item = &Tactic> {
        self.tactics.iter().map(|(t, _)| t)
    }
    pub fn featured_in_current(&self) -> &FeaturedInNode {
        match self.num_tactics_run.checked_sub(1) {
            Some(i) => &self.tactics[i].1,
            None => &self.featured_in_root,
        }
    }
    pub fn featured_in_current_mut(&mut self) -> &mut FeaturedInNode {
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
                .chain(iter::once((tactic, FeaturedInNode::Nothing)))
                .collect(),
            num_tactics_run: self.num_tactics_run + 1,
            ..self.clone()
        }
    }
}
