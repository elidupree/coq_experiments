pub mod display;
// mod from_constructors;
// mod metavariable_conversions;
// pub mod logic;
// pub mod prolog;
// pub mod derivers;
pub mod formula_types;
pub mod inference;
pub mod proof_hierarchy;
pub mod provers;
pub mod raw_proofs;
pub mod raw_proofs_ext;
// pub mod rules;
pub mod solver_pool;
// pub mod specialization;
// pub mod tuple_equality_tree;
pub mod proof_serialization;
pub mod uncurried_function;
pub mod unfolding;

#[allow(clippy::all)]
mod lalrpop_wrapper {
    use lalrpop_util::lalrpop_mod;
    lalrpop_mod!(pub(crate) introspective_calculus, "/introspective_calculus/introspective_calculus.rs");
}

pub use self::lalrpop_wrapper::introspective_calculus::{
    ExplicitRuleParser, FormulaParser, InferenceParser, NamedInferenceParser, ProofLineParser,
};
use std::collections::{btree_map, BTreeMap};
use std::fmt::Debug;
// use crate::introspective_calculus::metavariable_conversions::MetavariablesInjectionContext;
// use crate::metavariable::Environment;
// use live_prop_test::{live_prop_test, lpt_assert_eq};
// use regex::{Captures, Regex};
// use arrayvec::ArrayVec;
use crate::ad_hoc_lazy_static;
use hash_capsule::caching::{BackrefSet, CacheMap, Downgrade, SingleCache};
use hash_capsule::{
    define_hash_capsule_wrappers, BuildHasherForHashCapsules, CapsuleContents, HashCapsule,
    HashCapsuleWeak,
};
use itertools::Itertools;
use live_prop_test::live_prop_test;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use std::fs::File;
use std::hash::Hash;
use std::io::{BufRead, BufReader};
use std::iter::zip;
use std::ops::Deref;
use std::path::Path;
use std::sync::LazyLock;

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ExplicitRule {
    pub name: String,
    pub formula: Formula,
}

#[derive(
    Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Debug, Default, Serialize, Deserialize,
)]
pub enum AbstractionKind {
    #[default]
    Lambda,
    ForAll,
}

define_hash_capsule_wrappers!(Formula(), FormulaWeak, FormulaValue);

impl Default for Formula {
    fn default() -> Self {
        Formula::atom(Atom::Const)
    }
}

#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize)]
pub struct RWMFormula(Formula);

#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize)]
pub struct RawFormula(Formula);

impl Deref for RWMFormula {
    type Target = Formula;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Deref for RawFormula {
    type Target = Formula;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<Formula> for RWMFormula {
    fn from(value: Formula) -> Self {
        value.to_rwm()
    }
}

impl From<&Formula> for RWMFormula {
    fn from(value: &Formula) -> Self {
        value.to_rwm()
    }
}

impl From<&RWMFormula> for RWMFormula {
    fn from(value: &RWMFormula) -> Self {
        value.clone()
    }
}

impl From<RawFormula> for RWMFormula {
    fn from(value: RawFormula) -> Self {
        value.0.already_rwm().unwrap()
    }
}

impl From<&RawFormula> for RWMFormula {
    fn from(value: &RawFormula) -> Self {
        value.0.already_rwm().unwrap()
    }
}

impl From<RWMFormula> for Formula {
    fn from(value: RWMFormula) -> Self {
        value.0
    }
}

impl From<&RWMFormula> for Formula {
    fn from(value: &RWMFormula) -> Self {
        value.0.clone()
    }
}

impl From<RawFormula> for Formula {
    fn from(value: RawFormula) -> Self {
        value.0
    }
}

impl From<&RawFormula> for Formula {
    fn from(value: &RawFormula) -> Self {
        value.0.clone()
    }
}

impl From<&Formula> for Formula {
    fn from(value: &Formula) -> Self {
        value.clone()
    }
}

pub trait FormulaTrait:
    Clone
    + Eq
    + Hash
    + Ord
    + Debug
    + Default
    + Serialize
    + DeserializeOwned
    + ToFormula
    + TryFrom<Formula>
    + Into<Formula>
    + TryFrom<RWMFormula>
    + Into<RWMFormula>
    + Send
    + Sync
    + 'static
{
}
impl FormulaTrait for Formula {}
impl FormulaTrait for RWMFormula {}

#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Debug, Default)]
pub enum FormulaRawness {
    #[default]
    Raw,
    RawWithMetavariables,
    Pretty {
        raw_form: RWMFormula,
    },
}

// #[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Debug, Default, Serialize, Deserialize)]
// pub struct FormulaWithMetadata {
//     value: FormulaValue,
//     rawness: FormulaRawness,
// }

impl Downgrade<FormulaWeak> for RWMFormula {
    fn downgrade(&self) -> FormulaWeak {
        self.0.downgrade()
    }

    fn upgrade(weak: &FormulaWeak) -> Option<RWMFormula> {
        Formula::upgrade(weak).map(|f| f.to_rwm())
    }
}

impl CapsuleContents for FormulaValue {
    type Caches = FormulaCaches;
    fn cleanup(&mut self, self_weak: HashCapsuleWeak<FormulaValue>, caches: &mut Self::Caches) {
        let self_weak = FormulaWeak(self_weak);
        if let FormulaValue::Apply([a, b]) = self {
            a.caches.applications.forget(&b.downgrade());
        }
        caches.substitutions.cleanup(|subs, f| {
            if let Some(f) = f.upgrade() {
                f.caches
                    .substitution_backrefs
                    .forget(&(self_weak.clone(), subs));
            };
        });
        caches.substitution_backrefs.cleanup(|(f, subs)| {
            if let Some(f) = f.upgrade() {
                f.caches.substitutions.forget(&subs);
            };
        });
    }
}

#[derive(Default)]
pub struct FormulaCaches {
    rawness: SingleCache<FormulaRawness>,
    naive_size: SingleCache<u64>,
    applications: CacheMap<FormulaWeak, FormulaWeak, BuildHasherForHashCapsules>,
    substitutions: CacheMap<BTreeMap<String, FormulaWeak>, FormulaWeak>,
    substitution_backrefs: BackrefSet<(FormulaWeak, BTreeMap<String, FormulaWeak>)>,
}

#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum FormulaValue {
    Atom(Atom),
    Apply([Formula; 2]),

    And([Formula; 2]),
    Equals([Formula; 2]),
    Implies([Formula; 2]),
    Tuple(Vec<Formula>),

    NamedGlobal { name: String, value: Formula },

    Metavariable(String),
    NameAbstraction(AbstractionKind, String, Formula),
}
#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Debug)]
pub enum RWMFormulaValue {
    Atom(Atom),
    Apply([RWMFormula; 2]),
    Metavariable(String),
}
#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Debug)]
pub enum RawFormulaValue {
    Atom(Atom),
    Apply([RawFormula; 2]),
}

impl Default for FormulaValue {
    fn default() -> Self {
        FormulaValue::Atom(Atom::default())
    }
}

#[derive(
    Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Debug, Default, Serialize, Deserialize,
)]
pub enum Atom {
    Equals,
    #[default]
    Const,
    Fuse,
}

pub struct ArrowChain((AbstractionKind, String), Option<Box<ArrowChain>>);

impl ArrowChain {
    pub fn to_formula(self, body: Formula) -> Formula {
        let body = Formula::name_abstraction((self.0).0, (self.0).1, body);
        match self.1 {
            None => body,
            Some(next) => next.to_formula(body),
        }
    }
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
    ($l:tt & $r:tt) => {
        $crate::introspective_calculus::Formula::and([ic!($l), ic!($r)]).unwrap()
    };
    ($l:tt = $r:tt) => {
        $crate::introspective_calculus::Formula::equals([ic!($l), ic!($r)])
    };
    ($l:tt -> $r:tt) => {
        $crate::introspective_calculus::Formula::implies([ic!($l), ic!($r)]).unwrap()
    };
    ($l:tt,) => {
        $crate::introspective_calculus::Formula::tuple(vec![ic!($l)])
    };
    ($l:tt, $r:tt) => {
        $crate::introspective_calculus::Formula::tuple(vec![ic!($l), ic!($r)])
    };
    ($l:tt $r:tt) => {
        $crate::introspective_calculus::Formula::apply([ic!($l), ic!($r)])
    };
    ($l:tt $r:expr) => {
        $crate::introspective_calculus::Formula::apply([ic!($l), $r])
    };
    ($name:tt @ $val:tt) => {
        $crate::introspective_calculus::Formula::make_named_global($name.into(), ic!($val))
    };

    ($l:expr => $r:tt) => {
        $crate::introspective_calculus::Formula::name_abstraction($crate::introspective_calculus::AbstractionKind::Lambda, $l.to_string(), ic!($r))
    };
    (forall $l:expr, $r:tt) => {
        $crate::introspective_calculus::Formula::name_abstraction($crate::introspective_calculus::AbstractionKind::ForAll, $l.to_string(), ic!($r))
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
    (id) => {
        $crate::introspective_calculus::Formula::id()
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
    (@unpack_pattern_in [$formula:expr] ($l:tt, $r:tt) => $body:expr) => {
        if let $crate::introspective_calculus::FormulaValue::Tuple(children) = &$formula.value {
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
        let formula = {
            #[allow(unused_imports)]
            use $crate::introspective_calculus::ToFormula;
            $formula.to_formula()
        };
        $(match_ic!(@arm result [formula] $pattern => $arm));*
    }};
}

#[macro_export]
macro_rules! formula {
    ($f: literal) => {{
        $crate::ad_hoc_lazy_static!($crate::introspective_calculus::Formula)(|| $crate::introspective_calculus::FormulaParser::new().parse($f).unwrap())
    }};
    ($f: literal, {$($substitutions:tt)*}) => {{
        $crate::formula!($f).to_rwm().with_metavariables_replaced_rwm(&$crate::substitutions!{$($substitutions)*})
    }};
}

#[macro_export]
macro_rules! inf {
    ($f: literal) => {{
        $crate::ad_hoc_lazy_static!($crate::introspective_calculus::inference::PrettyInference)(|| $crate::introspective_calculus::InferenceParser::new().parse($f).unwrap())
    }};
    ($f: literal, {$($substitutions:tt)*}) => {{
        $crate::inf!($f).to_rwm().with_metavariables_replaced(&$crate::substitutions!{$($substitutions)*})
    }};
}

// pub struct InductiveTypeConstructor {
//     pub constructors: Vec<InductiveTypeConstructor>,
// }
// pub struct InductiveTypeDefinition {
//     pub constructors: Vec<InductiveTypeConstructor>,
// }

// pub struct GlobalContext {
//     pub definitions: BTreeMap<String, Arc<Formula>>,
//     pub inductive_type_definitions: BTreeMap<String, InductiveTypeDefinition>,
// }

static ID: LazyLock<Formula> = LazyLock::new(|| ic!("id" @ ((fuse const) const)));
static PROP_TRUE: LazyLock<Formula> =
    LazyLock::new(|| ic!("True" @ ({Formula::default()} = {Formula::default()})));
static ALL: LazyLock<Formula> =
    LazyLock::new(|| ic!("all" @ (equals (const {Formula::prop_true()}))));
// static AND: LazyLock<Formula> = LazyLock::new(|| ic!("And" @ (P => (((P A) B) = ((P True) True)))));
static PROP_FALSE: LazyLock<Formula> =
    LazyLock::new(|| ic!("False" @ ({Formula::all()} {Formula::id()})));

fn rawness_of_rwm_formulas(formulas: &[RWMFormula]) -> FormulaRawness {
    let mut result = FormulaRawness::Raw;
    for f in formulas {
        match f.rawness() {
            FormulaRawness::RawWithMetavariables => {
                result = FormulaRawness::RawWithMetavariables;
            }
            FormulaRawness::Pretty { .. } => {
                panic!()
            }
            _ => {}
        }
    }
    result
}

pub trait ToFormula {
    fn to_formula(&self) -> Formula;
}

impl ToFormula for str {
    fn to_formula(&self) -> Formula {
        Formula::metavariable(self.to_string())
    }
}

impl<T> ToFormula for T
where
    for<'a> &'a T: Into<Formula>,
{
    fn to_formula(&self) -> Formula {
        self.into()
    }
}

/***************************************************
                  Constructors
***************************************************/
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
        match atom {
            Atom::Equals => ad_hoc_lazy_static!(Formula)(|| {
                Formula(HashCapsule::new(FormulaValue::Atom(Atom::Equals)))
            })
            .clone(),
            Atom::Const => ad_hoc_lazy_static!(Formula)(|| {
                Formula(HashCapsule::new(FormulaValue::Atom(Atom::Const)))
            })
            .clone(),
            Atom::Fuse => ad_hoc_lazy_static!(Formula)(|| {
                Formula(HashCapsule::new(FormulaValue::Atom(Atom::Fuse)))
            })
            .clone(),
        }
    }
    pub fn metavariable(name: String) -> Formula {
        Formula::from(FormulaValue::Metavariable(name))
    }

    pub fn make_named_global(name: String, value: Formula) -> Formula {
        Formula::from(FormulaValue::NamedGlobal {
            name,
            value: value.clone(),
        })
    }
    pub fn apply(children: [Formula; 2]) -> Formula {
        children[0]
            .clone()
            .caches
            .applications
            .get(children[1].downgrade(), || {
                Formula::from(FormulaValue::Apply(children))
            })
    }
    pub fn and(children: [Formula; 2]) -> Result<Formula, String> {
        for child in &children {
            child
                .to_rwm()
                .as_eq_sides()
                .ok_or_else(|| format!("can't join non-equality formula `{child}` with `&`"))?;
        }
        Ok(Formula::from(FormulaValue::And(children)))
    }
    pub fn and_and_true(children: &[Formula]) -> Result<Formula, String> {
        let mut result = Formula::prop_true();
        for c in children.iter().rev() {
            result = Formula::and([c.clone(), result])?;
        }
        Ok(result)
    }
    pub fn equals(children: [Formula; 2]) -> Formula {
        Formula::from(FormulaValue::Equals(children))
    }
    pub fn implies(children: [Formula; 2]) -> Result<Formula, String> {
        for child in &children {
            child
                .to_rwm()
                .as_eq_sides()
                .ok_or_else(|| format!("can't join non-equality formula `{child}` with `->`"))?;
        }
        Ok(Formula::from(FormulaValue::Implies(children)))
    }
    pub fn tuple(children: Vec<Formula>) -> Formula {
        Formula::from(FormulaValue::Tuple(children))
    }
    pub fn name_abstraction(kind: AbstractionKind, name: String, body: Formula) -> Formula {
        Formula::from(FormulaValue::NameAbstraction(kind, name, body))
    }
}

/***************************************************
                  Various stuff?
***************************************************/

impl Formula {
    pub fn as_eq_sides(&self) -> Option<[Formula; 2]> {
        match_ic!(self, {
            ((equals a) b) => Some([a.clone(), b.clone()]),
            (a = b) => Some([a.clone(), b.clone()]),
            _ => None,
        })
    }

    pub fn rawness(&self) -> FormulaRawness {
        self.caches.rawness.get(|| match &self.value {
            FormulaValue::Atom(_) => FormulaRawness::Raw,
            FormulaValue::Apply([a, b]) => {
                if let [Some(a), Some(b)] = [a, b].map(Formula::already_rwm) {
                    rawness_of_rwm_formulas(&[a, b])
                } else {
                    FormulaRawness::Pretty {
                        raw_form: ic!({a.to_rwm()} {b.to_rwm()}).to_rwm(),
                    }
                }
            }
            FormulaValue::And([a, b]) => FormulaRawness::Pretty {
                raw_form: {
                    let [[al, ar], [bl, br]] = [a, b].map(|f| f.to_rwm().as_eq_sides().unwrap());
                    ic!((al, bl) = (ar, br)).to_rwm()
                },
            },
            FormulaValue::Equals([a, b]) => FormulaRawness::Pretty {
                raw_form: ic!((equals a) b).to_rwm(),
            },
            FormulaValue::Implies([a, b]) => FormulaRawness::Pretty {
                raw_form: ic!(a = (a & b)).to_rwm(),
            },
            FormulaValue::Tuple(children) => {
                let mut raw_form = ID.to_rwm();
                for c in children {
                    raw_form = ic!((fuse raw_form) (const c)).to_rwm();
                }

                FormulaRawness::Pretty { raw_form }
            }
            FormulaValue::NamedGlobal { value, .. } => FormulaRawness::Pretty {
                raw_form: value.to_rwm(),
            },
            FormulaValue::Metavariable(_) => FormulaRawness::RawWithMetavariables,
            FormulaValue::NameAbstraction(kind, name, body) => {
                let raw_abstracted_body = body.to_rwm().with_metavariable_abstracted(name);
                FormulaRawness::Pretty {
                    raw_form: match kind {
                        AbstractionKind::Lambda => raw_abstracted_body,
                        AbstractionKind::ForAll => ic!(ALL raw_abstracted_body).to_rwm(),
                    },
                }
            }
        })
    }
}

impl Formula {
    // pub fn value(&self) -> &FormulaValue {
    //     &self.value
    // }
    pub fn is_raw_with_metavariables(&self) -> bool {
        matches!(
            self.rawness(),
            FormulaRawness::Raw | FormulaRawness::RawWithMetavariables
        )
    }
    pub fn is_raw(&self) -> bool {
        matches!(self.rawness(), FormulaRawness::Raw)
    }
}
impl FormulaValue {
    pub fn children(&self) -> Vec<&Formula> {
        match self {
            FormulaValue::Atom(_) | FormulaValue::Metavariable(_) => Vec::new(),
            FormulaValue::Implies(f)
            | FormulaValue::Equals(f)
            | FormulaValue::And(f)
            | FormulaValue::Apply(f) => f.iter().collect(),
            FormulaValue::NamedGlobal { value, .. } => vec![value],
            FormulaValue::Tuple(children) => children.iter().collect(),
            FormulaValue::NameAbstraction(_kind, _name, body) => vec![body],
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
        match self {
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
        match self {
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

pub fn downgrade_substitutions(s: &BTreeMap<String, RWMFormula>) -> BTreeMap<String, FormulaWeak> {
    s.iter().map(|(k, v)| (k.clone(), v.downgrade())).collect()
}

impl RWMFormula {
    pub fn value(&self) -> RWMFormulaValue {
        match &self.0.value {
            FormulaValue::Atom(a) => RWMFormulaValue::Atom(*a),
            FormulaValue::Apply(children) => {
                RWMFormulaValue::Apply(children.each_ref().map(Formula::to_rwm))
            }
            FormulaValue::Metavariable(s) => RWMFormulaValue::Metavariable(s.clone()),
            _ => unreachable!("RWMFormula had non-RWM value {}", self),
        }
    }
    pub fn map_children_rwm(&self, mut map: impl FnMut(RWMFormula) -> RWMFormula) -> RWMFormula {
        self.map_children(|f| map(f.to_rwm()).into()).to_rwm()
    }
    pub fn as_eq_sides(&self) -> Option<[RWMFormula; 2]> {
        match_ic!(self, {
            ((equals a) b) => Some([a.to_rwm(), b.to_rwm()]),
            _ => None,
        })
    }
    pub fn other_eq_side(&self, first: &RWMFormula) -> Option<RWMFormula> {
        let [a, b] = self.as_eq_sides()?;
        if *first == a {
            Some(b)
        } else if *first == b {
            Some(a)
        } else {
            None
        }
    }

    pub fn with_metavariables_replaced_rwm(&self, replacements: &Substitutions) -> RWMFormula {
        let downgraded = downgrade_substitutions(replacements);
        let result = self
            .caches
            .substitutions
            .get(downgraded.clone(), || match &self.value {
                FormulaValue::Metavariable(n) => {
                    if let Some(replacement) = replacements.get(n) {
                        replacement.clone()
                    } else {
                        self.clone()
                    }
                }
                _ => self.map_children_rwm(|f| f.with_metavariables_replaced_rwm(replacements)),
            });
        result
            .caches
            .substitution_backrefs
            .insert(((**self).downgrade(), downgraded));
        // use std::cell::RefCell;
        // thread_local! {static RESULTS_CACHE:RefCell<HashMap<(RWMFormula, Substitutions), RWMFormula>> = RefCell::new(HashMap::new());}
        //
        // let key = (self.clone(), replacements.clone());
        // if let Some(result) =
        //     RESULTS_CACHE.with(|results_cache| results_cache.borrow().get(&key).cloned())
        // {
        //     return result;
        // }

        // RESULTS_CACHE.with(|results_cache| results_cache.borrow_mut().insert(key, result.clone()));
        result
    }
}
impl RawFormula {
    pub fn value(&self) -> RawFormulaValue {
        match &self.0.value {
            FormulaValue::Atom(a) => RawFormulaValue::Atom(*a),
            FormulaValue::Apply(children) => {
                RawFormulaValue::Apply(children.each_ref().map(|f| f.already_raw().unwrap()))
            }
            _ => unreachable!("RWMFormula had non-RWM value {}", self),
        }
    }
    pub fn as_eq_sides(&self) -> Option<[RawFormula; 2]> {
        match_ic!(self, {
            ((equals a) b) => Some([a.already_raw().unwrap(), b.already_raw().unwrap()]),
            _ => None,
        })
    }
}
//
// #[macro_export]
// macro_rules! substitutions {
//     ($($var:tt := $val:expr),*$(,)?) => {{
//         #[allow(unused_imports)]
//         use $crate::introspective_calculus::ToFormula;
//         [$(($var.to_string(), $val.to_formula())),*].into_iter().collect::<::std::collections::BTreeMap<String, Formula>>()
//     }};
// }

#[macro_export]
macro_rules! substitutions {
    (@ [$($sofar:tt)*]) => {{
        [$($sofar)*].into_iter().collect::<$crate::introspective_calculus::Substitutions>()
    }};
    (@ [$($sofar:tt)*] $var:ident := $val:expr, $($rest:tt)*) => {{
        $crate::substitutions!(@ [$($sofar)* (std::stringify!($var).to_string(), <_ as Into<$crate::introspective_calculus::RWMFormula>>::into($val)),] $($rest)*)
    }};
    (@ [$($sofar:tt)*] $var:ident : $val:expr, $($rest:tt)*) => {{
        $crate::substitutions!(@ [$($sofar)*] $var := $val, $($rest)*)
    }};
    (@ [$($sofar:tt)*] $val:ident, $($rest:tt)*) => {{
        $crate::substitutions!(@ [$($sofar)*] $val := $val, $($rest)*)
    }};
    (@ [$($sofar:tt)*] $var:ident := $val:expr) => {{
        $crate::substitutions!(@ [$($sofar)*] $var := $val,)
    }};
    (@ [$($sofar:tt)*] $var:ident : $val:expr) => {{
        $crate::substitutions!(@ [$($sofar)*] $var : $val,)
    }};
    (@ [$($sofar:tt)*] $val:ident) => {{
        $crate::substitutions!(@ [$($sofar)*] $val,)
    }};
    ($first:ident $($rest:tt)*) => {{
        $crate::substitutions!(@ [] $first $($rest)*)
    }};
}

pub type Substitutions = BTreeMap<String, RWMFormula>;

pub fn merge_substitution_into(
    substitutions: &mut Substitutions,
    name: &str,
    value: RWMFormula,
) -> Result<(), String> {
    match substitutions.entry(name.to_string()) {
        btree_map::Entry::Occupied(e) => {
            let existing = e.get();
            if existing.to_rwm() != value.to_rwm() {
                return Err(format!("Variable `{name}`, which was already assigned value `{existing}`, also needs conflicting value `{value}`"));
            }
        }
        btree_map::Entry::Vacant(e) => {
            e.insert(value);
        }
    }
    Ok(())
}

pub fn merge_substitutions_into(
    dst: &mut Substitutions,
    src: &Substitutions,
) -> Result<(), String> {
    for (name, value) in src {
        merge_substitution_into(dst, name, value.clone())?;
    }
    Ok(())
}

#[live_prop_test]
impl Formula {
    pub fn to_rwm(&self) -> RWMFormula {
        match self.rawness() {
            FormulaRawness::Pretty { raw_form } => raw_form,
            _ => RWMFormula(self.clone()),
        }
    }
    pub fn already_rwm(&self) -> Option<RWMFormula> {
        match self.rawness() {
            FormulaRawness::Pretty { .. } => None,
            _ => Some(RWMFormula(self.clone())),
        }
    }
    pub fn already_raw(&self) -> Option<RawFormula> {
        match &self.rawness() {
            FormulaRawness::Raw => Some(RawFormula(self.clone())),
            _ => None,
        }
    }
    pub fn to_raw(&self) -> Option<RawFormula> {
        self.to_rwm().already_raw()
    }
    pub fn map_children(&self, mut map: impl FnMut(&Formula) -> Formula) -> Formula {
        match &self.value {
            FormulaValue::Atom(_) | FormulaValue::Metavariable(_) => self.clone(),
            FormulaValue::And(f) => Formula::and(f.each_ref().map(map)).unwrap(),
            FormulaValue::Equals(f) => Formula::equals(f.each_ref().map(map)),
            FormulaValue::Implies(f) => Formula::implies(f.each_ref().map(map)).unwrap(),
            FormulaValue::Tuple(f) => Formula::tuple(f.iter().map(map).collect()),
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

    /// convenience function for using ic!() as a pattern
    pub fn matches<T: TryFrom<Vec<RWMFormula>>>(
        &self,
        other: impl Into<RWMFormula>,
    ) -> Result<T, String>
    where
        T::Error: Debug,
    {
        self.to_rwm()
            .substitutions_to_become(&other.into())
            .map(|map| {
                map.values()
                    .cloned()
                    .collect::<Vec<RWMFormula>>()
                    .try_into()
                    .unwrap()
            })
    }

    pub fn metavariables_to_arguments(&self, arguments: &[String]) -> Formula {
        let mut result = self.clone();
        for varname in arguments.iter().rev() {
            result = ic!(varname => self);
        }
        result
    }
}

impl RWMFormula {
    pub fn with_metavariable_abstracted(&self, name: &str) -> RWMFormula {
        if !self.contains_free_metavariable(name) {
            return ic!(const self).to_rwm();
        }
        match self.value() {
            RWMFormulaValue::Atom(_) => panic!("should've early-exited above"),
            RWMFormulaValue::Metavariable(n) => {
                assert_eq!(n, name, "should've early-exited above");
                Formula::id().to_rwm()
            }
            RWMFormulaValue::Apply(c) => {
                if matches!(&c[1].value, FormulaValue::Metavariable(n) if n == name)
                    && !c[0].contains_free_metavariable(name)
                {
                    c[0].to_rwm()
                } else {
                    let a = c[0].with_metavariable_abstracted(name);
                    let b = c[1].with_metavariable_abstracted(name);
                    ic!((fuse a) b).to_rwm()
                }
            }
        }
    }

    /// values for meta-variables such that the raw form of `self` would become exactly the specified raw form (not allowing definitional equality, but ignoring differences between pretty and raw forms)
    pub fn add_substitutions_to_become(
        &self,
        goal: &RWMFormula,
        substitutions: &mut Substitutions,
    ) -> Result<(), String> {
        match (self.value(), goal.value()) {
            (RWMFormulaValue::Atom(s), RWMFormulaValue::Atom(g)) => {
                if s != g {
                    return Err(format!(
                        "Tried to unify formulas with conflicting atoms: `{s} := {g}`"
                    ));
                }
            }
            (RWMFormulaValue::Metavariable(name), _) => {
                merge_substitution_into(substitutions, &name, goal.clone())?
            }
            (RWMFormulaValue::Apply(children), RWMFormulaValue::Apply(goal_children)) => {
                for (child, goal_child) in zip(children, goal_children) {
                    child.add_substitutions_to_become(&goal_child, substitutions)?;
                }
            }
            _ => return Err(format!("Could not unify `{self}` with `{goal}`")),
        }
        Ok(())
    }
    pub fn substitutions_to_become(&self, goal: &RWMFormula) -> Result<Substitutions, String> {
        let mut result = BTreeMap::new();
        self.add_substitutions_to_become(goal, &mut result)?;
        Ok(result)
    }

    pub fn metavariables_to_arguments(&self, arguments: &[String]) -> RWMFormula {
        self.0.metavariables_to_arguments(arguments).to_rwm()
    }

    pub fn simplest_function_equality_form(&self) -> RWMFormula {
        if let Ok([a, b]) = ic!("a" & "b").matches::<[RWMFormula; 2]>(self) {
            let [al, ar] = a.simplest_function_equality_form().as_eq_sides().unwrap();
            let [bl, br] = b.simplest_function_equality_form().as_eq_sides().unwrap();
            ic!((al, bl) = (ar, br)).to_rwm()
        } else if let Ok([a]) = ic!((const True) = "a").matches::<[RWMFormula; 1]>(self) {
            let varname = format!("FEF_Placeholder_{}", a.free_metavariables().len());
            let mut variableized = ic!(a {&varname}).to_rwm();
            variableized.unfold_until(1000);
            let [al, ar] = variableized
                .simplest_function_equality_form()
                .as_eq_sides()
                .unwrap();
            ic!(((&varname => al), (&varname => ar))).to_rwm()
        } else if self.as_eq_sides().is_some() {
            self.clone()
        } else {
            ic!(True = self).to_rwm()
        }
    }
}
impl Formula {
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

    pub fn with_metavariables_replaced(&self, replacements: &BTreeMap<String, Formula>) -> Formula {
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

    pub fn naive_size(&self) -> u64 {
        self.caches.naive_size.get(|| {
            let mut result = 1u64;
            for f in self.to_rwm().children() {
                result = result.saturating_add(f.naive_size());
            }
            result
        })
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
                name: format!("{}, internal", rule.name),
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

pub fn all_axioms() -> Vec<Formula> {
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
        .map(|r| Formula::make_named_global(r.name, r.formula.clone()))
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
//     pub definitions: BTreeMap<String, Formula>,
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
