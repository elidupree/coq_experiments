use crate::goals_analysis::{CoqValueInfo, Goals};
use crate::serapi_protocol::{ExnInfo, StateId};
use crate::tactics::Tactic;
use derivative::Derivative;
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::io::BufReader;
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
    pub application_state: Arc<Mutex<SharedState>>,
}

pub struct SertopThread {
    pub child_stdin: ChildStdin,
    pub lines_iterator: std::io::Lines<BufReader<ChildStdout>>,
    pub sertop_state: SertopState,
    pub application: Arc<Mutex<SharedState>>,
    pub last_added_file_code: String,
    pub end_of_first_added_from_file_that_failed_to_execute: Option<usize>,
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

#[derive(Debug)]
pub struct SertopState {
    pub added_from_file: Vec<AddedFromFile>,
    pub added_synthetic: Vec<AddedSynthetic>,
    pub num_executed_from_file: usize,
    pub num_executed_synthetic: usize,
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
