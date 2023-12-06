use crate::inf;
use crate::introspective_calculus::inference::Inference;
use crate::introspective_calculus::uncurried_function::UncurriedFunctionEquivalence;
use crate::introspective_calculus::{ExplicitRuleParser, RWMFormula, RawFormula, Substitutions};
use itertools::Itertools;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::iter::{once, zip};
use std::ops::Deref;
use std::sync::{Arc, LazyLock};

#[derive(Clone)]
pub struct RawProof(Arc<RawProofInner>);

pub struct RawProofInner {
    pub rule_instance: RuleRawInstance,
    pub premises: Vec<RawProof>,
}

impl Deref for RawProof {
    type Target = RawProofInner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub enum CleanExternalRule {
    EqSym,
    EqTrans,
    DefinitionOfConst,
    DefinitionOfFuse,
    SubstituteInLhs,
    SubstituteInRhs,
}
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct Axiom {
    pub specified_formula: RWMFormula,
    pub internal_form: UncurriedFunctionEquivalence,
}
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub enum StrengtheningRule {
    StrengthenSuccessor,
}
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub enum CleanRule {
    External(CleanExternalRule),
    Axiom(Axiom),
}
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub enum Rule {
    Clean(CleanRule),
    Strengthening(StrengtheningRule),
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct RuleInstance {
    pub rule: Rule,
    pub substitutions: Substitutions,
}
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct RuleRawInstance(RuleInstance);

impl Deref for RuleRawInstance {
    type Target = RuleInstance;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub trait RuleTrait {
    fn inference(&self) -> Inference;
}

impl RuleTrait for CleanExternalRule {
    fn inference(&self) -> Inference {
        match self {
            CleanExternalRule::EqSym => inf!("A = B |- B = A").to_rwm(),
            CleanExternalRule::EqTrans => inf!("A = B, B = C |- A = C").to_rwm(),
            CleanExternalRule::DefinitionOfConst => inf!("|- const A B = A").to_rwm(),
            CleanExternalRule::DefinitionOfFuse => inf!("|- fuse A B C = (A C) (B C)").to_rwm(),
            CleanExternalRule::SubstituteInLhs => inf!("A = B |- (A C) = (B C)").to_rwm(),
            CleanExternalRule::SubstituteInRhs => inf!("A = B |- (C A) = (C B)").to_rwm(),
        }
    }
}

impl RuleTrait for StrengtheningRule {
    fn inference(&self) -> Inference {
        match self {
            StrengtheningRule::StrengthenSuccessor => {
                inf!("const True = fuse (const equals) A B |- A = B").to_rwm()
            }
        }
    }
}

impl RuleTrait for Axiom {
    fn inference(&self) -> Inference {
        Inference::new(vec![], self.internal_form.formula().into())
    }
}

impl RuleTrait for CleanRule {
    fn inference(&self) -> Inference {
        match self {
            CleanRule::External(r) => r.inference(),
            CleanRule::Axiom(r) => r.inference(),
        }
    }
}

impl RuleTrait for Rule {
    fn inference(&self) -> Inference {
        match self {
            Rule::Clean(r) => r.inference(),
            Rule::Strengthening(r) => r.inference(),
        }
    }
}

macro_rules! rule_types {
    ($($Rule:ident),*) => {
        $(
impl Display for $Rule {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.inference().fmt(f)
    }
}
        )*
    }
}

rule_types!(Rule, CleanRule, CleanExternalRule, StrengtheningRule, Axiom);

impl Axiom {
    pub fn new(specified_formula: RWMFormula) -> Axiom {
        let sides = specified_formula.as_eq_sides().unwrap();
        let free_variables = specified_formula.free_metavariables();
        let num_variables = free_variables.len();
        let versions = free_variables
            .into_iter()
            .cloned()
            .permutations(num_variables)
            .map(|argument_order| UncurriedFunctionEquivalence {
                sides: sides.map(|s| s.to_uncurried_function_of(&argument_order)),
            });
        let internal_form = versions
            .min_by_key(|r| {
                r.sides
                    .map(|side| side.formula().naive_size())
                    .iter()
                    .sum::<usize>()
            })
            .unwrap();
        Axiom {
            specified_formula,
            internal_form,
        }
    }
}

impl From<CleanExternalRule> for Rule {
    fn from(value: CleanExternalRule) -> Self {
        Rule::Clean(CleanRule::External(value))
    }
}

impl Rule {
    pub fn specialize(&self, substitutions: Substitutions) -> RuleInstance {
        for variable in self.inference().free_metavariables() {
            if !substitutions.contains_key(&variable) {
                panic!("Tried to specialize rule {self} without specifying variable {variable}")
            }
        }
        RuleInstance {
            rule: self.clone(),
            substitutions,
        }
    }
}

fn lines(file: &mut impl BufRead) -> impl Iterator<Item = String> + '_ {
    file.lines()
        .map(Result::unwrap)
        .filter(|l| !l.chars().all(char::is_whitespace) && !l.starts_with('#'))
}

pub static EXTENSIONALITY_AXIOMS: LazyLock<BTreeMap<String, Axiom>> = LazyLock::new(|| {
    let parser = ExplicitRuleParser::new();
    let mut file = BufReader::new(File::open("./data/ic_axioms.ic").unwrap());
    lines(&mut file)
        .map(|l| match parser.parse(&l) {
            Ok(a) => (a.name.clone(), Axiom::new(a.formula.to_rwm())),
            Err(e) => panic!("Got error `{e}` while parsing rule `{l}`"),
        })
        .collect()
});

impl RuleInstance {
    pub fn assume_raw(self) -> RuleRawInstance {
        assert!(
            self.premises()
                .chain(once(self.conclusion()))
                .all(|f| f.is_raw()),
            "assumed non-raw instance was raw"
        );
        RuleRawInstance(self)
    }

    pub fn further_specialize(&self, substitutions: &Substitutions) -> RuleInstance {
        RuleInstance {
            rule: self.rule.clone(),
            substitutions: self
                .substitutions
                .iter()
                .map(|(k, v)| (k.clone(), v.with_metavariables_replaced_rwm(substitutions)))
                .collect(),
        }
    }

    pub fn premises(&self) -> impl Iterator<Item = RWMFormula> + '_ {
        self.rule
            .inference()
            .premises
            .clone()
            .into_iter()
            .map(|premise| premise.with_metavariables_replaced_rwm(&self.substitutions))
    }
    pub fn conclusion(&self) -> RWMFormula {
        self.rule
            .inference()
            .conclusion
            .with_metavariables_replaced_rwm(&self.substitutions)
    }
}

impl RuleRawInstance {
    pub fn premises(&self) -> impl Iterator<Item = RawFormula> + '_ {
        self.0
            .premises()
            .map(|premise| premise.already_raw().unwrap())
    }
    pub fn conclusion(&self) -> RawFormula {
        self.0.conclusion().already_raw().unwrap()
    }
    pub fn with_zero_variables(&self) -> RuleInstance {
        self.0.clone()
    }
}
impl RawProof {
    pub fn new(
        rule_instance: RuleRawInstance,
        premises: Vec<RawProof>,
    ) -> Result<RawProof, String> {
        let required_premises: Vec<RawFormula> = rule_instance.premises().collect();
        if premises.len() != required_premises.len() {
            return Err(format!(
                "Wrong number of premises to rule `{}` (need {}, got {})",
                rule_instance.rule,
                required_premises.len(),
                premises.len(),
            ));
        }
        for (required, provided) in zip(&required_premises, &premises) {
            if provided.conclusion() != *required {
                return Err(format!(
                    "Incorrect premise provided to rule {} (need {required}, got {})",
                    rule_instance.rule,
                    provided.conclusion(),
                ));
            }
        }
        Ok(RawProof(Arc::new(RawProofInner {
            rule_instance,
            premises,
        })))
    }

    pub fn conclusion(&self) -> RawFormula {
        self.rule_instance.conclusion()
    }
}
