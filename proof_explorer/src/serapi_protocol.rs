use derivative::Derivative;
use serde::{Deserialize, Serialize};

fn default<T: Default>() -> T {
    Default::default()
}
fn is_default<T: Default + PartialEq>(value: &T) -> bool {
    value == &T::default()
}

pub type Unfinished = ();

pub type StateId = i64;
pub type RouteId = i64;
pub type Constr = Unfinished;
pub type ConstrExpr = Unfinished;
pub type RawBacktrace = Unfinished;
pub type Exn = Unfinished;
pub type PrettyPrint = Unfinished;
#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct Location {
    line_nb: i64,
    bol_pos: i64,
    line_nb_last: i64,
    bol_pos_last: i64,
    bp: i64,
    ep: i64,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub enum CoqObject {
    CoqString(String),
    CoqSList(Vec<String>),
    CoqPp(PrettyPrint),
    CoqLoc(Location),
    CoqGoal(Constr),
    CoqExtGoal(ConstrExpr),
    // ...
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub enum PrintFormat {
    PpSer,
    PpStr,
    PpTex,
    PpCoq,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize, Derivative)]
#[derivative(Default)]
pub struct FormatOptions {
    #[derivative(Default(value = "PrintFormat::PpSer"))]
    pub pp_format: PrintFormat,
    pub pp_depth: i64,
    #[derivative(Default(value = "\"...\".to_string ()"))]
    pub pp_elide: String,
    #[derivative(Default(value = "72"))]
    pub pp_margin: i64,
}

#[derive(Clone, PartialEq, Eq, Debug, Default, Serialize, Deserialize)]
pub struct PrintOptions {
    pub sid: StateId,
    pub pp: FormatOptions,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub enum QueryPredicate {
    Prefix(String),
}

#[derive(Clone, PartialEq, Eq, Debug, Default, Serialize, Deserialize)]
pub struct QueryOptions {
    #[serde(skip_serializing_if = "is_default")]
    pub preds: Vec<QueryPredicate>,
    #[serde(skip_serializing_if = "is_default")]
    pub limit: Option<i64>,
    #[serde(skip_serializing_if = "is_default")]
    pub sid: StateId,
    #[serde(skip_serializing_if = "is_default")]
    pub pp: FormatOptions,
    #[serde(skip_serializing_if = "is_default")]
    pub route: RouteId,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub enum QueryCommand {
    Option,
    Search,
    Goals,
    EGoals,
    Ast,
    TypeOf(String),
    Names(String),
    Tactics(String),
    Locate(String),
    Implicits(String),
    Vernac(String),
    // ...
}

#[derive(Clone, PartialEq, Eq, Debug, Default, Serialize, Deserialize)]
pub struct ParseOptions {
    #[serde(skip_serializing_if = "is_default")]
    pub ontop: Option<StateId>,
}

#[derive(Clone, PartialEq, Eq, Debug, Default, Serialize, Deserialize)]
pub struct AddOptions {
    #[serde(skip_serializing_if = "is_default")]
    pub lim: Option<i64>,
    #[serde(skip_serializing_if = "is_default")]
    pub ontop: Option<StateId>,
    #[serde(skip_serializing_if = "is_default")]
    pub newtip: Option<StateId>,
    #[serde(skip_serializing_if = "is_default")]
    pub verb: bool,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub enum Command {
    NewDoc(Unfinished),
    Add(AddOptions, String),
    Cancel(Vec<StateId>),
    Exec(StateId),
    Query(QueryOptions, QueryCommand),
    Print(PrintOptions, CoqObject),
    Parse(ParseOptions, String),
    Join,
    Finish,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct ExnInfo {
    pub loc: Option<Location>,
    pub stm_ids: Option<(StateId, StateId)>,
    pub backtrace: RawBacktrace,
    pub exn: Exn,
    pub pp: PrettyPrint,
    pub str: String,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub enum AddedExtra {
    NewTip,
    Unfocus(StateId),
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub enum AnswerKind {
    Ack,
    Completed,
    Added(StateId, Location, AddedExtra),
    Canceled(Vec<StateId>),
    ObjList(Vec<CoqObject>),
    CoqExn(ExnInfo),
}

pub type CommandTag = String;
pub type TaggedCommand = (CommandTag, Command);

#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub enum FeedbackContent {
    Processed,
    Incomplete,
    Complete,
    ProcessingIn(String),
    InProgress(i64),
    WorkerStatus(String, String),
    AddedAxiom,
    FileDependency(Option<String>, String),
    FileLoaded(String, String),
    Message {
        level: i64,
        loc: Option<Location>,
        pp: PrettyPrint,
        str: String,
    },
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct Feedback {
    pub doc_id: i64,
    pub span_id: StateId,
    pub route: RouteId,
    pub contents: FeedbackContent,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub enum Answer {
    Feedback(Feedback),
    Answer(CommandTag, AnswerKind),
}
