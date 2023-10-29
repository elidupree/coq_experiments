pub mod display;
// mod from_constructors;
// mod metavariable_conversions;
pub mod logic;
// pub mod prolog;
pub mod inference;
pub mod unfolding;

#[allow(clippy::all)]
mod lalrpop_wrapper {
    use lalrpop_util::lalrpop_mod;
    lalrpop_mod!(pub(crate) introspective_calculus, "/introspective_calculus/introspective_calculus.rs");
}

pub use self::lalrpop_wrapper::introspective_calculus::{
    ExplicitRuleParser, FormulaParser, ProofLineParser,
};
use std::collections::{hash_map, HashMap};
// use crate::introspective_calculus::metavariable_conversions::MetavariablesInjectionContext;
// use crate::metavariable::Environment;
// use live_prop_test::{live_prop_test, lpt_assert_eq};
// use regex::{Captures, Regex};
use crate::introspective_calculus::logic::TrueFormula;
use arrayvec::ArrayVec;
use itertools::Itertools;
use live_prop_test::live_prop_test;
use serde::{Deserialize, Serialize};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::iter::zip;
use std::ops::Deref;
use std::path::Path;
use std::sync::{Arc, LazyLock};

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

#[derive(Clone, Eq, PartialEq, Hash, Debug, Default, Serialize, Deserialize)]
pub struct Formula(Arc<FormulaWithMetadata>);

impl Deref for Formula {
    type Target = FormulaWithMetadata;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Debug, Default, Serialize, Deserialize)]
pub enum FormulaRawness {
    #[default]
    Raw,
    RawWithMetavariables,
    Pretty {
        raw_form: Formula,
    },
}

#[derive(Clone, Eq, PartialEq, Hash, Debug, Default, Serialize, Deserialize)]
pub struct FormulaWithMetadata {
    pub value: FormulaValue,
    rawness: FormulaRawness,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug, Serialize, Deserialize)]
pub enum FormulaValue {
    Atom(Atom),
    Apply([Formula; 2]),

    And([Formula; 2]),
    Equals([Formula; 2]),
    Implies([Formula; 2]),

    NamedGlobal { name: String, value: Formula },

    Metavariable(String),
    NameAbstraction(AbstractionKind, String, Formula),
}

impl Default for FormulaValue {
    fn default() -> Self {
        FormulaValue::Atom(Atom::default())
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Default, Serialize, Deserialize)]
pub enum Atom {
    #[default]
    Equals,
    Const,
    Fuse,
}

/// It would be nice if we could just use the same "parsing" machinery for parts of the rust code,
/// but that's wasteful and injecting rust variables is hokey. On the flipside, constructing formulas
/// manually is way too verbose. So here's a macro to be a middle ground.
#[macro_export]
macro_rules! ic {
    ({$e:expr}) => {
        {
            #[allow(unused_imports)]
            use $crate::introspective_calculus::ToFormula;
            ($e).to_formula()
        }
    };
    (($($stuff:tt)+)) => {
        ic!($($stuff)+)
    };
    ($l:tt $r:tt) => {
        $crate::introspective_calculus::Formula::apply([ic!($l), ic!($r)])
    };
    ($l:tt & $r:tt) => {
        $crate::introspective_calculus::Formula::and([ic!($l), ic!($r)])
    };
    ($l:tt $r:expr) => {
        $crate::introspective_calculus::Formula::apply([ic!($l), $r])
    };
    ($l:tt = $r:tt) => {
        $crate::introspective_calculus::Formula::equals([ic!($l), ic!($r)])
    };
    ($l:tt -> $r:tt) => {
        $crate::introspective_calculus::Formula::implies([ic!($l), ic!($r)])
    };
    ($name:tt @ $val:tt) => {
        $crate::introspective_calculus::Formula::make_named_global($name.into(), ic!($val))
    };

    ($l:expr => $r:tt) => {
        $crate::introspective_calculus::Formula::name_abstraction(AbstractionKind::Lambda, $l.to_string(), ic!($r))
    };
    (forall $l:expr, $r:tt) => {
        $crate::introspective_calculus::Formula::name_abstraction(AbstractionKind::ForAll, $l.to_string(), ic!($r))
    };
    // (id) => {
    //     Formula::id()
    // };
    (True) => {
        $crate::introspective_calculus::Formula::prop_true()
    };
    // (And) => {
    //     $crate::introspective_calculus::Formula::and_function()
    // };
    (equals) => {
        $crate::introspective_calculus::Formula::atom($crate::introspective_calculus::Atom::Equals)
    };
    (const) => {
        $crate::introspective_calculus::Formula::atom($crate::introspective_calculus::Atom::Const)
    };
    (fuse) => {
        $crate::introspective_calculus::Formula::atom($crate::introspective_calculus::Atom::Fuse)
    };
    ($e:expr) => {
        {
            #[allow(unused_imports)]
            use $crate::introspective_calculus::ToFormula;
            ($e).to_formula()
        }
    };
}

#[macro_export]
macro_rules! match_ic {
    (@unpack_pattern_in [$formula:expr] equals => $body:expr) => {
        if $formula == &ic!(equals) {
            $body;
        }
    };
    (@unpack_pattern_in [$formula:expr] const => $body:expr) => {
        if $formula == &ic!(const) {
            $body;
        }
    };
    (@unpack_pattern_in [$formula:expr] fuse => $body:expr) => {
        if $formula == &ic!(fuse) {
            $body;
        }
    };
    (@unpack_pattern_in [$formula:expr] $var:ident => $body:expr) => {{
        let $var = $formula;
        $body;
    }};
    (@unpack_pattern_in [$formula:expr] ($l:tt $r:tt) => $body:expr) => {
        if let $crate::introspective_calculus::FormulaValue::Apply(children) = &$formula.value {
            match_ic!(@unpack_pattern_in [&children[0]] $l => match_ic!(@unpack_pattern_in [&children[1]] $r => $body))
        }
    };
    (@unpack_pattern_in [$formula:expr] ($l:tt & $r:tt) => $body:expr) => {
        if let $crate::introspective_calculus::FormulaValue::And(children) = &$formula.value {
            match_ic!(@unpack_pattern_in [&children[0]] $l => match_ic!(@unpack_pattern_in [&children[1]] $r => $body))
        }
    };
    (@unpack_pattern_in [$formula:expr] ($l:tt = $r:tt) => $body:expr) => {
        if let $crate::introspective_calculus::FormulaValue::Equals(children) = &$formula.value {
            match_ic!(@unpack_pattern_in [&children[0]] $l => match_ic!(@unpack_pattern_in [&children[1]] $r => $body))
        }
    };
    (@unpack_pattern_in [$formula:expr] ($l:tt -> $r:tt) => $body:expr) => {
        if let $crate::introspective_calculus::FormulaValue::Implies(children) = &$formula.value {
            match_ic!(@unpack_pattern_in [&children[0]] $l => match_ic!(@unpack_pattern_in [&children[1]] $r => $body))
        }
    };
    (@arm $result:ident [$formula:expr] _ => $arm:expr) => {{
        #[allow(unreachable_code)]
        if $result.is_none() {
            $result = Some($arm)
        }
        $result.unwrap()
    }};
    (@arm $result:ident [$formula:expr] $pattern:tt => $arm:expr) => {
        #[allow(unused_assignments)]
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

static ID: LazyLock<Formula> = LazyLock::new(|| ic!("id" @ ((fuse const) const)));
static PROP_TRUE: LazyLock<Formula> = LazyLock::new(|| ic!("True" @ ((equals equals) equals)));
static ALL: LazyLock<Formula> =
    LazyLock::new(|| ic!("all" @ (equals (const {Formula::prop_true()}))));
// static AND: LazyLock<Formula> = LazyLock::new(|| ic!("And" @ (P => (((P A) B) = ((P True) True)))));
static PROP_FALSE: LazyLock<Formula> =
    LazyLock::new(|| ic!("False" @ ({Formula::all()} {Formula::id()})));

fn rawness_of_raw_pair(pair: &[Formula; 2]) -> Option<FormulaRawness> {
    match pair.each_ref().map(|c| &c.rawness) {
        [FormulaRawness::Raw, FormulaRawness::Raw] => Some(FormulaRawness::Raw),
        [FormulaRawness::Pretty { .. }, _] | [_, FormulaRawness::Pretty { .. }] => None,
        _ => Some(FormulaRawness::RawWithMetavariables),
    }
}

pub trait ToFormula {
    fn to_formula(&self) -> Formula;
}

impl ToFormula for str {
    fn to_formula(&self) -> Formula {
        Formula::metavariable(self.to_string())
    }
}

impl ToFormula for Formula {
    fn to_formula(&self) -> Formula {
        self.clone()
    }
}

impl Formula {
    pub fn id() -> Formula {
        ID.clone()
    }
    pub fn prop_true() -> Formula {
        PROP_TRUE.clone()
    }
    pub fn all() -> Formula {
        ALL.clone()
    }
    // pub fn and_function() -> Formula {
    //     AND.clone()
    // }
    pub fn prop_false() -> Formula {
        PROP_FALSE.clone()
    }
    pub fn atom(atom: Atom) -> Formula {
        Formula(Arc::new(FormulaWithMetadata {
            value: FormulaValue::Atom(atom),
            rawness: FormulaRawness::Raw,
        }))
    }
    pub fn metavariable(name: String) -> Formula {
        Formula(Arc::new(FormulaWithMetadata {
            value: FormulaValue::Metavariable(name),
            rawness: FormulaRawness::RawWithMetavariables,
        }))
    }

    pub fn make_named_global(name: String, value: Formula) -> Formula {
        Formula(Arc::new(FormulaWithMetadata {
            value: FormulaValue::NamedGlobal {
                name,
                value: value.clone(),
            },
            rawness: FormulaRawness::Pretty {
                raw_form: value.to_raw_with_metavariables(),
            },
        }))
    }
    pub fn apply(children: [Formula; 2]) -> Formula {
        Formula(Arc::new({
            if let Some(rawness) = rawness_of_raw_pair(&children) {
                FormulaWithMetadata {
                    value: FormulaValue::Apply(children),
                    rawness,
                }
            } else {
                let raw_children = children.each_ref().map(|c| c.to_raw_with_metavariables());
                let raw_rawness = rawness_of_raw_pair(&raw_children).unwrap();
                let raw_form = Formula(Arc::new(FormulaWithMetadata {
                    value: FormulaValue::Apply(raw_children),
                    rawness: raw_rawness,
                }));
                FormulaWithMetadata {
                    value: FormulaValue::Apply(children),
                    rawness: FormulaRawness::Pretty { raw_form },
                }
            }
        }))
    }
    pub fn combine_pretty(
        children: [Formula; 2],
        combine: impl FnOnce([Formula; 2]) -> FormulaValue,
        combine_raw: impl FnOnce([Formula; 2]) -> FormulaValue,
    ) -> Formula {
        let raw_children = children.each_ref().map(|c| c.to_raw_with_metavariables());
        let raw_rawness = rawness_of_raw_pair(&raw_children).unwrap();
        let raw_form = Formula(Arc::new(FormulaWithMetadata {
            value: combine_raw(raw_children),
            rawness: raw_rawness,
        }));

        Formula(Arc::new(FormulaWithMetadata {
            value: combine(children),
            rawness: FormulaRawness::Pretty { raw_form },
        }))
    }
    pub fn and(children: [Formula; 2]) -> Formula {
        Formula::combine_pretty(children, FormulaValue::And, |[a, b]| {
            ic!(forall "P", ((("P" a) b) = (("P" True) True)))
                .as_raw_with_metavariables()
                .value
                .clone()
        })
    }
    pub fn equals(children: [Formula; 2]) -> Formula {
        Formula::combine_pretty(children, FormulaValue::Equals, |[a, b]| {
            ic!((equals a)b).value.clone()
        })
    }
    pub fn implies(children: [Formula; 2]) -> Formula {
        Formula::combine_pretty(children, FormulaValue::Implies, |[a, b]| {
            ic!((equals a)(a & b))
                .as_raw_with_metavariables()
                .value
                .clone()
        })
    }
    pub fn name_abstraction(kind: AbstractionKind, name: String, body: Formula) -> Formula {
        let raw_abstracted_body = body
            .as_raw_with_metavariables()
            .with_metavariable_abstracted(&name);
        Formula(Arc::new(FormulaWithMetadata {
            value: FormulaValue::NameAbstraction(kind, name, body),
            rawness: FormulaRawness::Pretty {
                raw_form: match kind {
                    AbstractionKind::Lambda => raw_abstracted_body,
                    AbstractionKind::ForAll => {
                        ic!({Formula::all().to_raw_with_metavariables()} raw_abstracted_body)
                    }
                },
            },
        }))
    }
    pub fn hard_coded_globals() -> HashMap<&'static str, Arc<Formula>> {
        // Formula::Id => ic!((fuse const) const),
        [].into_iter().collect()
    }
    pub fn as_eq_sides(&self) -> Option<[&Formula; 2]> {
        match_ic!(self, {
            ((equals a) b) => Some([a, b]),
            (a = b) => Some([a, b]),
            _ => None,
        })
    }
}
#[live_prop_test]
impl FormulaWithMetadata {
    pub fn is_raw_with_metavariables(&self) -> bool {
        matches!(
            self.rawness,
            FormulaRawness::Raw | FormulaRawness::RawWithMetavariables
        )
    }

    pub fn children(&self) -> ArrayVec<&Formula, 3> {
        match &self.value {
            FormulaValue::Atom(_) | FormulaValue::Metavariable(_) => ArrayVec::new(),
            FormulaValue::Implies(f)
            | FormulaValue::Equals(f)
            | FormulaValue::And(f)
            | FormulaValue::Apply(f) => f.iter().collect(),
            FormulaValue::NamedGlobal { value, .. } => [value].into_iter().collect(),
            FormulaValue::NameAbstraction(_kind, _name, body) => [body].into_iter().collect(),
        }
    }
    // pub fn children_mut(&mut self) -> ArrayVec<&mut Formula, 3> {
    //     match self {
    //         FormulaValue::EmptySet | FormulaValue::Id | FormulaValue::Atom(_) | FormulaValue::Metavariable(_) => {
    //             ArrayVec::new()
    //         }
    //         FormulaValue::Implies(f) | FormulaValue::Union(f) | FormulaValue::Apply(f) => f.iter_mut().collect(),
    //         FormulaValue::NameAbstraction(_name, body) => [&mut **body].into_iter().collect(),
    //     }
    // }

    pub fn contains_free_metavariable(&self, name: &str) -> bool {
        match &self.value {
            FormulaValue::Metavariable(n) => n == name,
            FormulaValue::NameAbstraction(_kind, n, body) => {
                n != name && body.contains_free_metavariable(name)
            }
            _ => self
                .children()
                .into_iter()
                .any(|f| f.contains_free_metavariable(name)),
        }
    }

    pub fn free_metavariables(&self) -> Vec<&String> {
        match &self.value {
            FormulaValue::Metavariable(n) => vec![n],
            FormulaValue::NameAbstraction(_kind, n, body) => {
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
}

#[live_prop_test]
impl Formula {
    pub fn as_raw_with_metavariables(&self) -> &Formula {
        match &self.rawness {
            FormulaRawness::Pretty { raw_form } => raw_form,
            _ => self,
        }
    }
    pub fn to_raw_with_metavariables(&self) -> Formula {
        self.as_raw_with_metavariables().clone()
    }
    pub fn map_children(&self, mut map: impl FnMut(&Formula) -> Formula) -> Formula {
        match &self.value {
            FormulaValue::Atom(_) | FormulaValue::Metavariable(_) => self.clone(),
            FormulaValue::And(f) => Formula::and(f.each_ref().map(map)),
            FormulaValue::Equals(f) => Formula::equals(f.each_ref().map(map)),
            FormulaValue::Implies(f) => Formula::implies(f.each_ref().map(map)),
            FormulaValue::Apply(f) => Formula::apply(f.each_ref().map(map)),
            FormulaValue::NamedGlobal { .. } => {
                // HACK: assume map_children is only used for metavariables stuff where named globals
                // don't need any attention because they don't contain metavariables
                self.clone()
            }
            FormulaValue::NameAbstraction(kind, name, body) => {
                Formula::name_abstraction(*kind, name.clone(), map(body))
            }
        }
    }

    // assumes already in raw form:
    #[live_prop_test(precondition = "self.is_raw_with_metavariables()")]
    pub fn with_metavariable_abstracted(&self, name: &str) -> Formula {
        if !self.contains_free_metavariable(name) {
            return ic!(const self.clone());
        }
        match &self.value {
            FormulaValue::Atom(_) => panic!("should've early-exited above"),
            FormulaValue::Metavariable(n) => {
                assert_eq!(n, name, "should've early-exited above");
                Formula::id().to_raw_with_metavariables()
            }
            FormulaValue::Apply(c) => {
                if matches!(&c[1].value, FormulaValue::Metavariable(n) if n == name)
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
        match &self.value {
            FormulaValue::Metavariable(n) => {
                if n == name {
                    replacement.clone()
                } else {
                    self.clone()
                }
            }
            _ => self.map_children(|f| f.with_metavariable_replaced(name, replacement)),
        }
    }

    pub fn with_metavariables_replaced(&self, replacements: &HashMap<String, Formula>) -> Formula {
        match &self.value {
            FormulaValue::Metavariable(n) => {
                if let Some(replacement) = replacements.get(n) {
                    replacement.clone()
                } else {
                    self.clone()
                }
            }
            _ => self.map_children(|f| f.with_metavariables_replaced(replacements)),
        }
    }

    pub fn with_metavariables_universalized<'a>(
        &self,
        variables: impl IntoIterator<Item = &'a str>,
    ) -> Formula {
        let mut result = self.clone();
        for variable in variables {
            // result = result.with_metavariable_abstracted(variable);
            // result = ic!({Formula::all()} result);
            result =
                Formula::name_abstraction(AbstractionKind::ForAll, variable.to_string(), result);
        }
        result
    }

    /// values for meta-variables such that the raw form of `self` would become exactly the specified raw form (not allowing definitional equality, but ignoring differences between pretty and raw forms)
    pub fn add_substitutions_to_become(
        &self,
        goal: &Formula,
        substitutions: &mut HashMap<String, Formula>,
    ) -> Result<(), String> {
        match (
            &self.as_raw_with_metavariables().value,
            &goal.as_raw_with_metavariables().value,
        ) {
            (FormulaValue::Atom(s), FormulaValue::Atom(g)) => {
                if s != g {
                    return Err(format!(
                        "Tried to unify formulas with conflicting atoms: `{s} := {g}`"
                    ));
                }
            }
            (FormulaValue::Metavariable(name), _) => match substitutions.entry(name.clone()) {
                hash_map::Entry::Occupied(e) => {
                    let existing = e.get();
                    if existing.as_raw_with_metavariables() != goal.as_raw_with_metavariables() {
                        return Err(format!("Variable `{name}`, which was already assigned value `{existing}`, also needs conflicting value `{goal}`"));
                    }
                }
                hash_map::Entry::Vacant(e) => {
                    e.insert(goal.clone());
                }
            },
            (FormulaValue::Apply(children), FormulaValue::Apply(goal_children)) => {
                for (child, goal_child) in zip(children, goal_children) {
                    child.add_substitutions_to_become(goal_child, substitutions)?;
                }
            }
            _ => return Err(format!("Could not unify `{self}` with `{goal}`")),
        }
        Ok(())
    }

    pub fn naive_size(&self) -> usize {
        1 + self
            .as_raw_with_metavariables()
            .children()
            .into_iter()
            .map(Formula::naive_size)
            .sum::<usize>()
    }

    // pub fn left_atom(&self) -> Atom {
    //     match self {
    //         FormulaValue::Atom(a) => *a,
    //         FormulaValue::Apply(c) => c[0].left_atom(),
    //         FormulaValue::Implies(_) => Atom::Implies,
    //         FormulaValue::And(_) => Atom::And,
    //         FormulaValue::Id => Atom::Fuse,
    //         FormulaValue::EmptySet => Atom::EmptySet,
    //         FormulaValue::Metavariable(_) => {
    //             panic!("can't call left_atom on a metavariable!")
    //         }
    //         FormulaValue::NameAbstraction(_, _, _) => Atom::Fuse, // TODO: technically wrong
    //     }
    // }

    // /// basically "unfold (self variable_name)"
    // pub fn combinators_to_variable_usages(&self, variable_name: &str) -> Formula {
    //     match_ic!(self, {
    //         ((fuse const) const) => FormulaValue::Metavariable(variable_name.into()),
    //         id => FormulaValue::Metavariable(variable_name.into()),
    //         ((fuse a) b) => {
    //             let a = a.combinators_to_variable_usages(variable_name);
    //             let b = b.combinators_to_variable_usages(variable_name);
    //             ic!(a b)
    //         },
    //         (const a) => {
    //             a.clone()
    //         },
    //         _ => ic!((self.clone()) FormulaValue::Metavariable(variable_name.into())),
    //     })
    // }

    // pub fn prettify(&self, next_name: char) -> Formula {
    //     let next_next_name = std::char::from_u32(next_name as u32 + 1).unwrap_or(next_name);
    //     match_ic!(self, {
    //         (all f) => Formula::NameAbstraction(AbstractionKind::ForAll,next_name.to_string(),f.combinators_to_variable_usages (&next_name.to_string()).prettify(next_next_name).into()),
    //         ((fuse const) const) => Formula::Id,
    //         ((fuse _a) _b) => Formula::NameAbstraction(AbstractionKind::Lambda,next_name.to_string(),self.combinators_to_variable_usages (&next_name.to_string()).prettify(next_next_name).into()),
    //         (const _a) => Formula::NameAbstraction(AbstractionKind::Lambda,next_name.to_string(),self.combinators_to_variable_usages (&next_name.to_string()).prettify(next_next_name).into()),
    //         ((and a) b) => ic!((a.prettify(next_name)) + (b.prettify(next_name))),
    //         ((implies a) b) => ic!((a.prettify(next_name)) -> (b.prettify(next_name))),
    //         empty_set => ic!(0),
    //         _ => self.map_children(|c|c.prettify(next_name))
    //     })
    // }
}

pub fn load_explicit_rules(path: impl AsRef<Path>) -> Vec<ExplicitRule> {
    let parser = ExplicitRuleParser::new();
    BufReader::new(File::open(path).unwrap())
        .lines()
        .map(Result::unwrap)
        .filter(|l| !l.chars().all(char::is_whitespace) && !l.starts_with('#'))
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
            //let c = rule.formula.to_raw_with_metavariables();
            let free_variables = rule.formula.free_metavariables();
            let versions = free_variables
                .iter()
                .copied()
                .permutations(free_variables.len())
                .map(|permutation| {
                    let result = rule.formula.with_metavariables_universalized(
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

pub fn all_axioms() -> Vec<TrueFormula> {
    let explicit_rules = load_explicit_rules("data/ic_axioms.ic");
    // for r in &mut rules_of_deduction {
    //     r.formula = ic!((implies empty_set) r.formula.clone());
    // }
    // let mut result = internalized_rules(&rules_of_deduction);
    // let extra_rules = internalized_rules(&load_explicit_rules("data/ic_extra_rules.ic"));
    // result.extend(extra_rules);
    // result
    internalized_rules(&explicit_rules)
        .into_iter()
        .map(|r| TrueFormula::axiom(Formula::make_named_global(r.name, r.formula)))
        .collect()
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
