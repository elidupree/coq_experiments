use crate::ic;
use crate::introspective_calculus::inference::Inference;
use crate::introspective_calculus::{InferenceParser, RWMFormula, RawFormula, Substitutions};
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
    pub rule_instance: ExternalRuleRawInstance,
    pub premises: Vec<RawProof>,
}

#[derive(Clone)]
pub struct ExternalRule(Inference);
#[derive(Clone)]
pub struct ExternalRuleInstance {
    pub rule: ExternalRule,
    pub substitutions: Substitutions,
}
#[derive(Clone)]
pub struct ExternalRuleRawInstance(ExternalRuleInstance);
#[derive(Clone)]
pub struct CleanExternalRule(ExternalRule);
#[derive(Clone)]
pub struct CleanExternalRuleInstance(ExternalRuleInstance);

impl Display for ExternalRule {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Deref for RawProof {
    type Target = RawProofInner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Deref for ExternalRule {
    type Target = Inference;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Deref for CleanExternalRule {
    type Target = ExternalRule;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Deref for ExternalRuleRawInstance {
    type Target = ExternalRuleInstance;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Deref for CleanExternalRuleInstance {
    type Target = ExternalRuleInstance;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

fn lines(file: &mut impl BufRead) -> impl Iterator<Item = String> + '_ {
    file.lines()
        .map(Result::unwrap)
        .filter(|l| !l.chars().all(char::is_whitespace) && !l.starts_with('#'))
}

pub static CLEAN_EXTERNAL_RULES: LazyLock<BTreeMap<String, CleanExternalRule>> =
    LazyLock::new(|| {
        let parser = InferenceParser::new();
        let mut file = BufReader::new(File::open("./data/ic_clean_external_rules.ic").unwrap());
        lines(&mut file)
            .map(|l| match parser.parse(&l) {
                Ok(a) => (a.name.clone(), CleanExternalRule(ExternalRule(a.to_rwm()))),
                Err(e) => panic!("Got error `{e}` while parsing rule `{l}`"),
            })
            .collect()
    });

pub static ALL_EXTERNAL_RULES: LazyLock<BTreeMap<String, ExternalRule>> = LazyLock::new(|| {
    let mut result: BTreeMap<String, ExternalRule> = CLEAN_EXTERNAL_RULES
        .iter()
        .map(|(key, value)| (key.clone(), value.0.clone()))
        .collect();
    result.insert(
        "strengthen: successor".to_string(),
        ExternalRule(Inference::new(
            vec![ic!(True = ("A" = "B")).to_rwm()],
            ic!("A" = "B").to_rwm(),
        )),
    );
    result
});

impl ExternalRule {
    pub fn specialize(&self, substitutions: Substitutions) -> ExternalRuleInstance {
        for variable in self.free_metavariables() {
            if !substitutions.contains_key(&variable) {
                panic!(
                        "Tried to specialize external rule {self} without specifying variable {variable}"
                    )
            }
        }
        ExternalRuleInstance {
            rule: self.clone(),
            substitutions,
        }
    }
}

impl CleanExternalRule {
    pub fn specialize(&self, substitutions: Substitutions) -> CleanExternalRuleInstance {
        CleanExternalRuleInstance(self.0.specialize(substitutions))
    }
}

impl ExternalRuleInstance {
    pub fn assume_raw(self) -> ExternalRuleRawInstance {
        assert!(
            self.premises()
                .chain(once(self.conclusion()))
                .all(|f| f.is_raw()),
            "assumed non-raw instance was raw"
        );
        ExternalRuleRawInstance(self)
    }

    pub fn further_specialize(&self, substitutions: &Substitutions) -> ExternalRuleInstance {
        ExternalRuleInstance {
            rule: self.rule.clone(),
            substitutions: self
                .substitutions
                .iter()
                .map(|(k, v)| (k.clone(), v.with_metavariables_replaced_rwm(substitutions)))
                .collect(),
        }
    }
}

impl ExternalRuleInstance {
    pub fn premises(&self) -> impl Iterator<Item = RWMFormula> + '_ {
        self.rule
            .premises
            .iter()
            .map(|premise| premise.with_metavariables_replaced_rwm(&self.substitutions))
    }
    pub fn conclusion(&self) -> RWMFormula {
        self.rule
            .conclusion
            .with_metavariables_replaced_rwm(&self.substitutions)
    }
}

impl ExternalRuleRawInstance {
    pub fn premises(&self) -> impl Iterator<Item = RawFormula> + '_ {
        self.rule.premises.iter().map(|premise| {
            premise
                .with_metavariables_replaced_rwm(&self.substitutions)
                .already_raw()
                .unwrap()
        })
    }
    pub fn conclusion(&self) -> RawFormula {
        self.rule
            .conclusion
            .with_metavariables_replaced_rwm(&self.substitutions)
            .already_raw()
            .unwrap()
    }
}
impl RawProof {
    pub fn new(
        rule_instance: ExternalRuleRawInstance,
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
