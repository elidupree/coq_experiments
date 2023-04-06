// mod display;
// mod from_constructors;
// mod metavariable_conversions;
// pub mod unfolding;

#[allow(clippy::all)]
mod lalrpop_wrapper {
    use lalrpop_util::lalrpop_mod;
    lalrpop_mod!(pub(crate) introspective_calculus, "/introspective_calculus/introspective_calculus.rs");
}

pub use self::lalrpop_wrapper::introspective_calculus::{
    FormulaParser, OrdinaryAxiomDefinitionParser,
};
// use crate::introspective_calculus::metavariable_conversions::MetavariablesInjectionContext;
// use crate::metavariable::Environment;
// use live_prop_test::{live_prop_test, lpt_assert_eq};
// use regex::{Captures, Regex};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct AxiomDefinition {
    pub name: String,
    pub premises: Vec<Formula>,
    pub conclusion: Formula,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Implies {
    pub level: Formula,
    pub antecedent: Formula,
    pub consequent: Formula,
}
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Substitution {
    pub original: Formula,
    pub index: Formula,
    pub replacement: Formula,
}
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Formula {
    Atom(Atom),
    Abstraction(Box<Formula>),
    Pop(Box<Formula>),
    Apply(Box<[Formula; 2]>),

    Level0,
    LevelSuccessor(Box<Formula>),
    Implies(Box<Implies>),
    Equals(Box<[Formula; 2]>),
    Substitution(Box<Substitution>),

    Metavariable(String),
    NameAbstraction(String, Box<Formula>),
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Atom {
    Level0,
    LevelSuccessor,
    Implies,
    Equals,
    Usage,
    SubstituteIn,
    ProofInduction,
}

pub fn load_ordinary_axioms(path: impl AsRef<Path>) -> Vec<AxiomDefinition> {
    let parser = OrdinaryAxiomDefinitionParser::new();
    BufReader::new(File::open(path).unwrap())
        .lines()
        .map(|l| parser.parse(&l.unwrap()).unwrap())
        .collect()
}

// #[derive(Clone, Eq, PartialEq, Debug)]
// pub enum Command {
//     AxiomDefinition(AxiomDefinition),
//     AssignGlobal(String, Formula),
//     AssertTrue(Formula),
// }
//
// pub struct Document {
//     commands: Vec<Command>,
// }
//
// pub struct GlobalContext {
//     pub definitions: HashMap<String, Formula>,
// }
//
// fn command_regex() -> Regex {
//     Regex::new(r"(?m)^>([^\.]*)\.").unwrap()
// }
//
// impl Document {
//     pub fn parse(text: &str) -> Self {
//         let re = command_regex();
//         let mut commands = Vec::new();
//         for captures in re.captures_iter(text) {
//             let command_text = captures.get(1).unwrap().as_str();
//             commands.push(Command::parse(command_text));
//         }
//         Document { commands }
//     }
//     pub fn reformat(text: &str) -> Cow<str> {
//         let re = command_regex();
//         re.replace_all(text, |captures: &Captures| {
//             let command_text = captures.get(1).unwrap().as_str();
//             format!(
//                 "> {}.",
//                 Command::parse(command_text)
//                     .to_display_item()
//                     .display_to_string()
//             )
//         })
//     }
//     pub fn inject_into(&self, environment: &mut Environment) {
//         let mut injector = MetavariablesInjectionContext::for_environment(environment);
//         injector.inject_commands(&self.commands);
//     }
//     pub fn into_globals(self) -> GlobalContext {
//         GlobalContext {
//             definitions: self
//                 .commands
//                 .into_iter()
//                 .filter_map(|command| match command {
//                     Command::ClaimType(_, _) => None,
//                     Command::Assign(name, formula) => Some((name, formula)),
//                 })
//                 .collect(),
//         }
//     }
// }
//
// #[live_prop_test]
// impl Command {
//     #[live_prop_test(postcondition = "result.check_roundtrips()")]
//     pub fn parse(text: &str) -> Self {
//         let parser = CommandParser::new();
//         match parser.parse(text) {
//             Ok(command) => command,
//             Err(e) => panic!("While parsing:\n    {text}\nGot error:\n    {e}"),
//         }
//     }
//     fn check_roundtrips(&self) -> Result<(), String> {
//         let text = self.to_string();
//         let result = CommandParser::new().parse(&text).map_err(|e| {
//             format!("Failed parsing generated text:\n    {text}\nWith error:\n    {e}")
//         })?;
//         lpt_assert_eq!(
//             self,
//             &result,
//             "Roundtrip mismatch with generated text:\n    {text}"
//         );
//         let text = self.to_display_item().display_to_string();
//         let result = CommandParser::new().parse(&text).map_err(|e| {
//             format!("Failed parsing generated text:\n    {text}\nWith error:\n    {e}")
//         })?;
//         lpt_assert_eq!(
//             self,
//             &result,
//             "Roundtrip mismatch with generated text:\n    {text}"
//         );
//         Ok(())
//     }
// }
//
// #[test]
// fn tests() {
//     use AbstractionKind::*;
//     use Command::*;
//     use Formula::{Apply, Hole, Prop, Usage};
//     let tests = [(
//         "Foo := λP:ℙ, ∀p:P, (p _)",
//         Assign(
//             "Foo".to_owned(),
//             Formula::Abstraction(Box::new(Abstraction {
//                 kind: Lambda,
//                 parameter_name: "P".to_string(),
//                 parameter_type: Prop,
//                 body: Formula::Abstraction(Box::new(Abstraction {
//                     kind: ForAll,
//                     parameter_name: "p".to_string(),
//                     parameter_type: Usage("P".to_string()),
//                     body: Apply(Box::new([Usage("p".to_string()), Hole])),
//                 })),
//             })),
//         ),
//     )];
//     for (text, command) in tests {
//         assert_eq!(CommandParser::new().parse(text).unwrap(), command)
//     }
// }
//
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn check_ordinary_axioms() {
        load_ordinary_axioms("data/ic_ordinary_axioms.ic");
    }
}
