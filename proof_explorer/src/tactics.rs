use serde::{Deserialize, Serialize};
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct Tactic {
    string: String,
}

impl Tactic {
    pub fn from_string(string: String) -> Tactic {
        Tactic { string }
    }
    pub fn human_string(&self) -> String {
        self.string.clone()
    }
    pub fn coq_string(&self) -> String {
        format!("progress {}", self.string)
    }
}
