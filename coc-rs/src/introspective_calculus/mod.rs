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

pub use self::lalrpop_wrapper::introspective_calculus::{ExplicitRuleParser, FormulaParser};
use std::collections::HashMap;
// use crate::introspective_calculus::metavariable_conversions::MetavariablesInjectionContext;
// use crate::metavariable::Environment;
// use live_prop_test::{live_prop_test, lpt_assert_eq};
// use regex::{Captures, Regex};
use arrayvec::ArrayVec;
use itertools::Itertools;
use live_prop_test::live_prop_test;
use serde::{Deserialize, Serialize};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;
use std::sync::Arc;

#[derive(Clone, Eq, PartialEq, Debug, Serialize, Deserialize)]
pub struct ExplicitRule {
    pub name: String,
    pub formula: Formula,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Default, Serialize, Deserialize)]
pub enum AbstractionKind {
    #[default]
    Lambda,
    ForAll,
}

#[derive(Clone, Eq, PartialEq, Debug, Default, Serialize, Deserialize)]
pub enum Formula {
    Atom(Atom),
    Apply(Arc<[Formula; 2]>),

    Implies(Arc<[Formula; 2]>),
    Union(Arc<[Formula; 2]>),
    #[default]
    Id,
    EmptySet,

    Metavariable(String),
    NameAbstraction(AbstractionKind, String, Arc<Formula>),
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Default, Serialize, Deserialize)]
pub enum Atom {
    Implies,
    #[default]
    EmptySet,
    Union,
    All,
    Const,
    Fuse,
}

/// It would be nice if we could just use the same "parsing" machinery for parts of the rust code,
/// but that's wasteful and injecting rust variables is hokey. On the flipside, constructing formulas
/// manually is way too verbose. So here's a macro to be a middle ground.
#[macro_export]
macro_rules! ic {
    (($($stuff:tt)+)) => {
        ic!($($stuff)+)
    };
    ($l:tt $r:tt) => {
        Formula::Apply(Arc::new([ic!($l), ic!($r)]))
    };
    ($l:tt $r:expr) => {
        Formula::Apply(Arc::new([ic!($l), $r]))
    };
    ($l:tt + $r:tt) => {
        Formula::Union(Arc::new([ic!($l), ic!($r)]))
    };
    ($l:tt -> $r:tt) => {
        Formula::Implies(Arc::new([ic!($l), ic!($r)]))
    };
    // ($l:expr => $r:tt) => {
    //     Formula::NameAbstraction(AbstractionKind::Lambda, $l, Arc::new(ic!($r)))
    // };
    // (∀ $l:expr, $r:tt) => {
    //     Formula::NameAbstraction(AbstractionKind::ForAll, $l, Arc::new(ic!($r)))
    // };
    (id) => {
        Formula::Id
    };
    (0) => {
        Formula::EmptySet
    };
    (implies) => {
        Formula::Atom(Atom::Implies)
    };
    (empty_set) => {
        Formula::Atom(Atom::EmptySet)
    };
    (union) => {
        Formula::Atom(Atom::Union)
    };
    (all) => {
        Formula::Atom(Atom::All)
    };
    (const) => {
        Formula::Atom(Atom::Const)
    };
    (fuse) => {
        Formula::Atom(Atom::Fuse)
    };
    ($e:expr) => {
        $e
    };
}

#[macro_export]
macro_rules! match_ic {
    (@unpack_pattern_in [$formula:expr] id => $body:expr) => {
        if let ic!(id) = $formula {
            $body;
        }
    };
    (@unpack_pattern_in [$formula:expr] 0 => $body:expr) => {
        if let ic!(0) = $formula {
            $body;
        }
    };
    (@unpack_pattern_in [$formula:expr] empty_set => $body:expr) => {
        if let ic!(empty_set) = $formula {
            $body;
        }
    };
    (@unpack_pattern_in [$formula:expr] union => $body:expr) => {
        if let ic!(union) = $formula {
            $body;
        }
    };
    (@unpack_pattern_in [$formula:expr] all => $body:expr) => {
        if let ic!(all) = $formula {
            $body;
        }
    };
    (@unpack_pattern_in [$formula:expr] implies => $body:expr) => {
        if let ic!(implies) = $formula {
            $body;
        }
    };
    (@unpack_pattern_in [$formula:expr] const => $body:expr) => {
        if let ic!(const) = $formula {
            $body;
        }
    };
    (@unpack_pattern_in [$formula:expr] fuse => $body:expr) => {
        if let ic!(fuse) = $formula {
            $body;
        }
    };
    (@unpack_pattern_in [$formula:expr] $var:ident => $body:expr) => {{
        let $var = $formula;
        $body;
    }};
    (@unpack_pattern_in [$formula:expr] ($l:tt $r:tt) => $body:expr) => {
        if let Formula::Apply(children) = $formula {
            match_ic!(@unpack_pattern_in [&children[0]] $l => match_ic!(@unpack_pattern_in [&children[1]] $r => $body))
        }
    };
    (@arm $result:ident [$formula:expr] _ => $arm:expr) => {{
        if $result.is_none() {
            $result = Some($arm)
        }
        $result.unwrap()
    }};
    (@arm $result:ident [$formula:expr] $pattern:tt => $arm:expr) => {
        if $result.is_none() {
            match_ic!(@unpack_pattern_in [$formula] $pattern => {
                $result = Some($arm);
            })
        }
    };
    ($formula:expr, {$($pattern:tt => $arm:expr),*$(,)*}) => {{
        let mut result = None;
        $(match_ic!(@arm result [$formula] $pattern => $arm));*
    }};
}

pub struct InductiveTypeConstructor {
    pub constructors: Vec<InductiveTypeConstructor>,
}
pub struct InductiveTypeDefinition {
    pub constructors: Vec<InductiveTypeConstructor>,
}

pub struct GlobalContext {
    pub definitions: HashMap<String, Arc<Formula>>,
    pub inductive_type_definitions: HashMap<String, InductiveTypeDefinition>,
}

#[live_prop_test]
impl Formula {
    // should be idempotent:
    #[live_prop_test(postcondition = "result.to_raw_with_metavariables() == result")]
    pub fn to_raw_with_metavariables(&self) -> Formula {
        match self {
            Formula::EmptySet => Formula::Atom(Atom::EmptySet),
            Formula::Id => ic!((fuse const) const),
            Formula::Implies(f) => {
                let a = f[0].to_raw_with_metavariables();
                let b = f[1].to_raw_with_metavariables();
                ic!((implies a)b)
            }
            Formula::Union(f) => {
                let a = f[0].to_raw_with_metavariables();
                let b = f[1].to_raw_with_metavariables();
                ic!((union a)b)
            }
            Formula::NameAbstraction(kind, name, body) => {
                let body = body
                    .to_raw_with_metavariables()
                    .with_metavariable_abstracted(name);
                match kind {
                    AbstractionKind::Lambda => body,
                    AbstractionKind::ForAll => {
                        ic!(all body)
                    }
                }
            }
            _ => self.map_children(Formula::to_raw_with_metavariables),
        }
    }

    pub fn is_raw_with_metavariables(&self) -> bool {
        self.to_raw_with_metavariables() == *self
    }

    pub fn children(&self) -> ArrayVec<&Formula, 3> {
        match self {
            Formula::EmptySet | Formula::Id | Formula::Atom(_) | Formula::Metavariable(_) => {
                ArrayVec::new()
            }
            Formula::Implies(f) | Formula::Union(f) | Formula::Apply(f) => f.iter().collect(),
            Formula::NameAbstraction(_kind, _name, body) => [&**body].into_iter().collect(),
        }
    }
    // pub fn children_mut(&mut self) -> ArrayVec<&mut Formula, 3> {
    //     match self {
    //         Formula::EmptySet | Formula::Id | Formula::Atom(_) | Formula::Metavariable(_) => {
    //             ArrayVec::new()
    //         }
    //         Formula::Implies(f) | Formula::Union(f) | Formula::Apply(f) => f.iter_mut().collect(),
    //         Formula::NameAbstraction(_name, body) => [&mut **body].into_iter().collect(),
    //     }
    // }

    pub fn map_children(&self, mut map: impl FnMut(&Formula) -> Formula) -> Formula {
        match self {
            Formula::EmptySet | Formula::Id | Formula::Atom(_) | Formula::Metavariable(_) => {
                self.clone()
            }
            Formula::Implies(f) => Formula::Implies(Arc::new(f.each_ref().map(map))),
            Formula::Union(f) => Formula::Union(Arc::new(f.each_ref().map(map))),
            Formula::Apply(f) => Formula::Apply(Arc::new(f.each_ref().map(map))),
            Formula::NameAbstraction(kind, name, body) => {
                Formula::NameAbstraction(*kind, name.clone(), Arc::new(map(body)))
            }
        }
    }

    pub fn contains_free_metavariable(&self, name: &str) -> bool {
        match self {
            Formula::Metavariable(n) => n == name,
            Formula::NameAbstraction(_kind, n, body) => {
                n != name && body.contains_free_metavariable(name)
            }
            _ => self
                .children()
                .into_iter()
                .any(|f| f.contains_free_metavariable(name)),
        }
    }

    pub fn free_metavariables(&self) -> Vec<&String> {
        match self {
            Formula::Metavariable(n) => vec![n],
            Formula::NameAbstraction(_kind, n, body) => {
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
            return ic!(const self.clone());
        }
        match self {
            Formula::Atom(_) => panic!("should've early-exited above"),
            Formula::Metavariable(n) => {
                assert_eq!(n, name, "should've early-exited above");
                Formula::Id.to_raw_with_metavariables()
            }
            Formula::Apply(c) => {
                if matches!(&c[1], Formula::Metavariable(n) if n == name)
                    && !c[0].contains_free_metavariable(name)
                {
                    c[0].clone()
                } else {
                    let a = c[0].with_metavariable_abstracted(name);
                    let b = c[1].with_metavariable_abstracted(name);
                    ic!((fuse a) b)
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

    pub fn with_metavariables_universalized<'a>(
        &self,
        variables: impl IntoIterator<Item = &'a str>,
    ) -> Formula {
        let mut result = self.clone();
        for variable in variables {
            result = result.with_metavariable_abstracted(variable);
            result = ic!(all result);
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

    pub fn left_atom(&self) -> Atom {
        match self {
            Formula::Atom(a) => *a,
            Formula::Apply(c) => c[0].left_atom(),
            Formula::Implies(_) => Atom::Implies,
            Formula::Union(_) => Atom::Union,
            Formula::Id => Atom::Fuse,
            Formula::EmptySet => Atom::EmptySet,
            Formula::Metavariable(_) => {
                panic!("can't call left_atom on a metavariable!")
            }
            Formula::NameAbstraction(_, _, _) => Atom::Fuse, // TODO: technically wrong
        }
    }

    /// basically "unfold (self variable_name)"
    pub fn combinators_to_variable_usages(&self, variable_name: &str) -> Formula {
        match_ic!(self, {
            ((fuse const) const) => Formula::Metavariable(variable_name.into()),
            id => Formula::Metavariable(variable_name.into()),
            ((fuse a) b) => {
                let a = a.combinators_to_variable_usages(variable_name);
                let b = b.combinators_to_variable_usages(variable_name);
                ic!(a b)
            },
            (const a) => {
                a.clone()
            },
            _ => ic!((self.clone()) Formula::Metavariable(variable_name.into())),
        })
    }

    pub fn prettify(&self, next_name: char) -> Formula {
        let next_next_name = std::char::from_u32(next_name as u32 + 1).unwrap_or(next_name);
        match_ic!(self, {
            (all f) => Formula::NameAbstraction(AbstractionKind::ForAll,next_name.to_string(),f.combinators_to_variable_usages (&next_name.to_string()).prettify(next_next_name).into()),
            ((fuse const) const) => Formula::Id,
            ((fuse _a) _b) => Formula::NameAbstraction(AbstractionKind::Lambda,next_name.to_string(),self.combinators_to_variable_usages (&next_name.to_string()).prettify(next_next_name).into()),
            (const _a) => Formula::NameAbstraction(AbstractionKind::Lambda,next_name.to_string(),self.combinators_to_variable_usages (&next_name.to_string()).prettify(next_next_name).into()),
            ((union a) b) => ic!((a.prettify(next_name)) + (b.prettify(next_name))),
            ((implies a) b) => ic!((a.prettify(next_name)) -> (b.prettify(next_name))),
            empty_set => ic!(0),
            _ => self.map_children(|c|c.prettify(next_name))
        })
    }
}

pub fn load_explicit_rules(path: impl AsRef<Path>) -> Vec<ExplicitRule> {
    let parser = ExplicitRuleParser::new();
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

pub fn internalized_rules(original_rules: &[ExplicitRule]) -> Vec<ExplicitRule> {
    original_rules
        .iter()
        .map(|rule| {
            let c = rule.formula.to_raw_with_metavariables();
            let free_variables = c.free_metavariables();
            let versions = free_variables
                .iter()
                .copied()
                .permutations(free_variables.len())
                .map(|permutation| {
                    let result = c.with_metavariables_universalized(
                        permutation
                            .iter()
                            .rev()
                            .copied()
                            .map(std::ops::Deref::deref),
                    );

                    // let mut unfolding = result.clone();
                    // for name in permutation {
                    //     unfolding = Formula::Apply(Arc::new([
                    //         unfolding,
                    //         Formula::Metavariable(name.clone()),
                    //     ]));
                    // }
                    // unfolding.unfold_until(1000);
                    // let mut unfolding2 = c.clone();
                    // unfolding2.unfold_until(1000);
                    // assert_eq!(unfolding, unfolding2, "Failed on rule {}", rule.name);

                    result
                });
            ExplicitRule {
                name: format!("{}", rule.name),
                formula: versions.min_by_key(Formula::naive_size).unwrap(),
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
            //     reconstruction = Formula::Apply(Arc::new([
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
//
// pub fn definition_of_proof_induction(generalized_axioms: &[ExplicitRule]) -> Formula {
//     let parser = FormulaParser::new();
//     let first_part = parser
//         .parse("induction_on_proofs = (P => (P ->0 (R => n => rest)))")
//         .unwrap();
//     let last_part = parser.parse("(R induction_on_proofs) ->0 (A => B => R A ->n R (A B)) ->0 (A => B => R (A ->0 B) ->n R A ->n R B) ->(n+1) R P").unwrap();
//     let mut rest = last_part;
//     for axiom in generalized_axioms {
//         rest = parser
//             .parse("R axiom ->0 rest")
//             .unwrap()
//             .with_metavariable_replaced("axiom", &axiom.conclusion)
//             .with_metavariable_replaced("rest", &rest);
//     }
//     first_part.with_metavariable_replaced("rest", &rest)
// }

pub fn all_official_rules() -> Vec<ExplicitRule> {
    let explicit_rules = load_explicit_rules("data/ic_rules_of_deduction.ic");
    let internalized_rules = internalized_rules(&explicit_rules);
    //let proof_induction = definition_of_proof_induction(&generalized_axioms);
    // let mut axioms = ordinary_axioms;
    // axioms.extend(generalized_axioms);
    // axioms.push(ExplicitRule {
    //     name: "definition of proof induction".to_string(),
    //     premises: vec![],
    //     conclusion: proof_induction,
    // });
    #[allow(clippy::let_and_return)]
    internalized_rules
}

// #[derive(Clone, Eq, PartialEq, Debug)]
// pub enum Command {
//     ExplicitRule(ExplicitRule),
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
//             Formula::Abstraction(Arc::new(Abstraction {
//                 kind: Lambda,
//                 parameter_name: "P".to_string(),
//                 parameter_type: Prop,
//                 body: Formula::Abstraction(Arc::new(Abstraction {
//                     kind: ForAll,
//                     parameter_name: "p".to_string(),
//                     parameter_type: Usage("P".to_string()),
//                     body: Apply(Arc::new([Usage("p".to_string()), Hole])),
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
        let rules = all_official_rules();
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
