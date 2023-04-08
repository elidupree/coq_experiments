// mod display;
// mod from_constructors;
// mod metavariable_conversions;
// pub mod unfolding;

pub mod prolog;

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
use live_prop_test::live_prop_test;
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
pub struct Abstraction {
    pub body: Formula,
    pub index: Formula,
}
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Formula {
    Atom(Atom),
    Abstraction(Box<Abstraction>),
    Pop(Box<Formula>),
    Apply(Box<[Formula; 2]>),

    Level0,
    LevelSuccessor(Box<Formula>),
    Implies(Box<Implies>),
    Equals(Box<[Formula; 2]>),

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
    ProofInduction,
}

#[live_prop_test]
impl Formula {
    // should be idempotent:
    #[live_prop_test(postcondition = "result.to_raw_with_metavariables() == result")]
    pub fn to_raw_with_metavariables(&self) -> Formula {
        match self {
            Formula::Level0 => Formula::Atom(Atom::Level0),
            Formula::LevelSuccessor(f) => Formula::Apply(Box::new([
                Formula::Atom(Atom::LevelSuccessor),
                f.to_raw_with_metavariables(),
            ])),
            Formula::Equals(f) => Formula::Apply(Box::new([
                Formula::Apply(Box::new([
                    Formula::Atom(Atom::Equals),
                    f[0].to_raw_with_metavariables(),
                ])),
                f[1].to_raw_with_metavariables(),
            ])),
            Formula::Implies(i) => Formula::Apply(Box::new([
                Formula::Apply(Box::new([
                    Formula::Apply(Box::new([
                        Formula::Atom(Atom::Implies),
                        i.level.to_raw_with_metavariables(),
                    ])),
                    i.antecedent.to_raw_with_metavariables(),
                ])),
                i.consequent.to_raw_with_metavariables(),
            ])),
            Formula::NameAbstraction(name, body) => Formula::Abstraction(Box::new(Abstraction {
                body: body
                    .to_raw_with_metavariables()
                    .with_metavariable_internalized(name, 0),
                index: Formula::Level0.to_raw_with_metavariables(),
            })),
            _ => self.map_children(Formula::to_raw_with_metavariables),
        }
    }

    pub fn is_raw_with_metavariables(&self) -> bool {
        self.to_raw_with_metavariables() == *self
    }

    pub fn map_children(&self, mut map: impl FnMut(&Formula) -> Formula) -> Formula {
        match self {
            Formula::Level0 | Formula::Atom(_) | Formula::Metavariable(_) => self.clone(),
            Formula::Pop(f) => Formula::Pop(Box::new(map(f))),
            Formula::LevelSuccessor(f) => Formula::LevelSuccessor(Box::new(map(f))),
            Formula::Equals(f) => Formula::Equals(Box::new(f.each_ref().map(map))),
            Formula::Apply(f) => Formula::Apply(Box::new(f.each_ref().map(map))),
            Formula::Abstraction(a) => Formula::Abstraction(Box::new(Abstraction {
                body: map(&a.body),
                index: map(&a.index),
            })),
            Formula::Implies(i) => Formula::Implies(Box::new(Implies {
                level: map(&i.level),
                antecedent: map(&i.antecedent),
                consequent: map(&i.consequent),
            })),
            Formula::NameAbstraction(name, body) => {
                Formula::NameAbstraction(name.clone(), Box::new(map(body)))
            }
        }
    }

    pub fn contains_free_metavariable(&self, name: &str) -> bool {
        match self {
            Formula::Metavariable(n) => n == name,
            Formula::Atom(_) | Formula::Level0 => false,
            Formula::Pop(f) | Formula::LevelSuccessor(f) => f.contains_free_metavariable(name),
            Formula::Equals(f) | Formula::Apply(f) => {
                f.iter().any(|f| f.contains_free_metavariable(name))
            }
            Formula::Abstraction(a) => {
                a.index.contains_free_metavariable(name) || a.body.contains_free_metavariable(name)
            }
            Formula::Implies(i) => {
                i.level.contains_free_metavariable(name)
                    || i.antecedent.contains_free_metavariable(name)
                    || i.consequent.contains_free_metavariable(name)
            }
            Formula::NameAbstraction(n, body) => n != name && body.contains_free_metavariable(name),
        }
    }

    // assumes already in raw form:
    #[live_prop_test(precondition = "self.is_raw_with_metavariables()")]
    pub fn with_metavariable_internalized(&self, name: &str, level: usize) -> Formula {
        if level == 0 && !self.contains_free_metavariable(name) {
            return Formula::Pop(Box::new(self.clone()));
        }
        match self {
            Formula::Metavariable(n) => {
                assert_eq!(n, name, "should already be popped");
                assert_eq!(level, 0);
                Formula::Atom(Atom::Usage)
            }
            Formula::Atom(_) => panic!("should already be popped"),
            Formula::Pop(f) => {
                assert!(level > 0, "shouldn't be pre-popped");
                Formula::Pop(Box::new(f.with_metavariable_internalized(name, level - 1)))
            }
            Formula::Apply(_) => {
                self.map_children(|f| f.with_metavariable_internalized(name, level))
            }
            Formula::Abstraction(a) => Formula::Abstraction(Box::new(Abstraction {
                body: a.body.with_metavariable_internalized(name, level + 1),
                index: a.index.with_metavariable_internalized(name, level),
            })),
            _ => panic!("should already be raw"),
        }
    }
}

pub fn load_ordinary_axioms(path: impl AsRef<Path>) -> Vec<AxiomDefinition> {
    let parser = OrdinaryAxiomDefinitionParser::new();
    BufReader::new(File::open(path).unwrap())
        .lines()
        .map(|l| {
            let l = l.unwrap();
            match parser.parse(&l) {
                Ok(a) => a,
                Err(e) => panic!("Got error `{e}` while parsing axiom `{l}`"),
            }
        })
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
        let axioms = load_ordinary_axioms("data/ic_ordinary_axioms.ic");
        // panic!(
        //     "{:?}",
        //     axioms
        //         .iter()
        //         .map(|a| a
        //             .conclusion
        //             .to_raw_with_metavariables()
        //             .as_prolog()
        //             .to_string())
        //         .collect::<Vec<_>>()
        // );
    }
    // #[test]
    // fn prolog_thing() {
    //     use swipl::prelude::*;
    //     fn foo() -> PrologResult<()> {
    //         let activation = initialize_swipl().unwrap();
    //         let context: Context<_> = activation.into();
    //
    //         let term = term! {context: hello(world)}?;
    //
    //         context.call_once(pred!(writeq / 1), [&term])?;
    //         context.call_once(pred!(nl / 0), [])?;
    //
    //         Ok(())
    //     }
    //     foo().unwrap();
    // }
}
