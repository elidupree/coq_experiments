pub mod display;
// mod from_constructors;
// mod metavariable_conversions;
pub mod prolog;
pub mod unfolding;

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
use arrayvec::ArrayVec;
use itertools::Itertools;
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
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub enum Formula {
    Atom(Atom),
    Apply(Box<[Formula; 2]>),

    Level0,
    LevelSuccessor(Box<Formula>),
    Implies(Box<Implies>),
    Equals(Box<[Formula; 2]>),
    #[default]
    Id,

    Metavariable(String),
    NameAbstraction(String, Box<Formula>),
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Atom {
    Level0,
    LevelSuccessor,
    Implies,
    Equals,
    Const,
    Fuse,
    InductionOnProofs,
}

#[live_prop_test]
impl Formula {
    // should be idempotent:
    #[live_prop_test(postcondition = "result.to_raw_with_metavariables() == result")]
    pub fn to_raw_with_metavariables(&self) -> Formula {
        match self {
            Formula::Level0 => Formula::Atom(Atom::Level0),
            Formula::Id => Formula::Apply(Box::new([
                Formula::Apply(Box::new([
                    Formula::Atom(Atom::Fuse),
                    Formula::Atom(Atom::Const),
                ])),
                Formula::Atom(Atom::Const),
            ])),
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
            Formula::NameAbstraction(name, body) => body
                .to_raw_with_metavariables()
                .with_metavariable_abstracted(name),
            _ => self.map_children(Formula::to_raw_with_metavariables),
        }
    }

    pub fn is_raw_with_metavariables(&self) -> bool {
        self.to_raw_with_metavariables() == *self
    }

    pub fn children(&self) -> ArrayVec<&Formula, 3> {
        match self {
            Formula::Level0 | Formula::Id | Formula::Atom(_) | Formula::Metavariable(_) => {
                ArrayVec::new()
            }
            Formula::LevelSuccessor(f) => [&**f].into_iter().collect(),
            Formula::Equals(f) | Formula::Apply(f) => f.iter().collect(),
            Formula::Implies(i) => ArrayVec::from([&i.level, &i.antecedent, &i.consequent]),
            Formula::NameAbstraction(_name, body) => [&**body].into_iter().collect(),
        }
    }
    pub fn children_mut(&mut self) -> ArrayVec<&mut Formula, 3> {
        match self {
            Formula::Level0 | Formula::Id | Formula::Atom(_) | Formula::Metavariable(_) => {
                ArrayVec::new()
            }
            Formula::LevelSuccessor(f) => [&mut **f].into_iter().collect(),
            Formula::Equals(f) | Formula::Apply(f) => f.iter_mut().collect(),
            Formula::Implies(i) => {
                ArrayVec::from([&mut i.level, &mut i.antecedent, &mut i.consequent])
            }
            Formula::NameAbstraction(_name, body) => [&mut **body].into_iter().collect(),
        }
    }

    pub fn map_children(&self, mut map: impl FnMut(&Formula) -> Formula) -> Formula {
        match self {
            Formula::Level0 | Formula::Id | Formula::Atom(_) | Formula::Metavariable(_) => {
                self.clone()
            }
            Formula::LevelSuccessor(f) => Formula::LevelSuccessor(Box::new(map(f))),
            Formula::Equals(f) => Formula::Equals(Box::new(f.each_ref().map(map))),
            Formula::Apply(f) => Formula::Apply(Box::new(f.each_ref().map(map))),
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
            Formula::NameAbstraction(n, body) => n != name && body.contains_free_metavariable(name),
            _ => self
                .children()
                .into_iter()
                .any(|f| f.contains_free_metavariable(name)),
        }
    }

    pub fn free_metavariables(&self) -> Vec<&String> {
        match self {
            Formula::Metavariable(n) => vec![n],
            Formula::NameAbstraction(n, body) => {
                let mut result = body.free_metavariables();
                result.retain(|&v| v != n);
                result
            }
            _ => {
                let mut result = Vec::new();
                for child in self.children() {
                    for variable in child.free_metavariables() {
                        if !result.contains(&variable) {
                            result.push(variable);
                        }
                    }
                }
                result
            }
        }
    }

    // assumes already in raw form:
    #[live_prop_test(precondition = "self.is_raw_with_metavariables()")]
    pub fn with_metavariable_abstracted(&self, name: &str) -> Formula {
        if !self.contains_free_metavariable(name) {
            return Formula::Apply(Box::new([Formula::Atom(Atom::Const), self.clone()]));
        }
        match self {
            Formula::Atom(_) => panic!("should've early-exited above"),
            Formula::Metavariable(n) => {
                assert_eq!(n, name, "should've early-exited above");
                Formula::Id.to_raw_with_metavariables()
            }
            Formula::Apply(a) => {
                if matches!(&a[1], Formula::Metavariable(n) if n == name)
                    && !a[0].contains_free_metavariable(name)
                {
                    a[0].clone()
                } else {
                    Formula::Apply(Box::new([
                        Formula::Apply(Box::new([
                            Formula::Atom(Atom::Fuse),
                            a[0].with_metavariable_abstracted(name),
                        ])),
                        a[1].with_metavariable_abstracted(name),
                    ]))
                }
            }
            _ => panic!("should already be raw"),
        }
    }

    pub fn with_metavariable_replaced(&self, name: &str, replacement: &Formula) -> Formula {
        match self {
            Formula::Metavariable(n) => {
                if n == name {
                    replacement.clone()
                } else {
                    self.clone()
                }
            }
            _ => self.map_children(|f| f.with_metavariable_replaced(name, replacement)),
        }
    }

    pub fn with_metavariables_abstracted<'a>(
        &self,
        variables: impl IntoIterator<Item = &'a str>,
    ) -> Formula {
        let mut result = self.clone();
        for variable in variables {
            result = result.with_metavariable_abstracted(variable);
        }
        result
    }

    pub fn naive_size(&self) -> usize {
        1 + self
            .children()
            .into_iter()
            .map(Formula::naive_size)
            .sum::<usize>()
    }
}

pub fn load_ordinary_axioms(path: impl AsRef<Path>) -> Vec<AxiomDefinition> {
    let parser = OrdinaryAxiomDefinitionParser::new();
    BufReader::new(File::open(path).unwrap())
        .lines()
        .map(Result::unwrap)
        .filter(|l| !l.chars().all(char::is_whitespace))
        .map(|l| match parser.parse(&l) {
            Ok(a) => a,
            Err(e) => panic!("Got error `{e}` while parsing axiom `{l}`"),
        })
        .collect()
}

pub fn generalized_axioms(ordinary_axioms: &[AxiomDefinition]) -> Vec<AxiomDefinition> {
    ordinary_axioms
        .iter()
        .map(|axiom| {
            let c = axiom.conclusion.to_raw_with_metavariables();
            let free_variables = c.free_metavariables();
            let versions = free_variables
                .iter()
                .copied()
                .permutations(free_variables.len())
                .map(|permutation| {
                    c.with_metavariables_abstracted(
                        permutation.iter().copied().map(std::ops::Deref::deref),
                    )
                });
            AxiomDefinition {
                name: format!("{}, generalized", axiom.name),
                premises: vec![],
                conclusion: versions.min_by_key(Formula::naive_size).unwrap(),
            }

            // eprintln!("{}", c.as_shorthand());
            // for permutation in free_variables
            //     .iter()
            //     .copied()
            //     .permutations(free_variables.len())
            // {
            //     let abstracted = c.with_metavariables_abstracted(
            //         permutation.iter().copied().map(std::ops::Deref::deref),
            //     );
            // eprintln!(
            //     "{:?}, {}, {}",
            //     permutation,
            //     abstracted.naive_size(),
            //     abstracted.as_shorthand()
            // );
            // let mut reconstruction = abstracted;
            // for &variable in permutation.iter().rev() {
            //     reconstruction = Formula::Apply(Box::new([
            //         reconstruction,
            //         Formula::Metavariable(variable.clone()),
            //     ]));
            // }
            // reconstruction.unfold_until(999);
            // eprintln!("{}", reconstruction.as_shorthand());
            // }
            // eprintln!();
        })
        .collect()
}

pub fn definition_of_proof_induction(generalized_axioms: &[AxiomDefinition]) -> Formula {
    let parser = FormulaParser::new();
    let first_part = parser
        .parse("induction_on_proofs = (P => (P ->0 (R => n => rest)))")
        .unwrap();
    let last_part = parser.parse("(R induction_on_proofs) ->0 (A => B => R A ->n R (A B)) ->0 (A => B => R (A ->0 B) ->n R A ->n R B) ->(n+1) R P").unwrap();
    let mut rest = last_part;
    for axiom in generalized_axioms {
        rest = parser
            .parse("R axiom ->0 rest")
            .unwrap()
            .with_metavariable_replaced("axiom", &axiom.conclusion)
            .with_metavariable_replaced("rest", &rest);
    }
    first_part.with_metavariable_replaced("rest", &rest)
}

pub fn all_axioms(path: impl AsRef<Path>) -> Vec<AxiomDefinition> {
    let ordinary_axioms = load_ordinary_axioms(path);
    let generalized_axioms = generalized_axioms(&ordinary_axioms);
    let proof_induction = definition_of_proof_induction(&generalized_axioms);
    let mut axioms = ordinary_axioms;
    axioms.extend(generalized_axioms);
    axioms.push(AxiomDefinition {
        name: "definition of proof induction".to_string(),
        premises: vec![],
        conclusion: proof_induction,
    });
    axioms
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
    fn check_axioms() {
        let axioms = all_axioms("data/ic_ordinary_axioms.ic");
        // for a in axioms {
        //     eprintln!(
        //         "{}",
        //         a.conclusion.to_raw_with_metavariables().as_shorthand()
        //     )
        // }
        // panic!();
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
