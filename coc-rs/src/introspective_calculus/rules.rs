use crate::ic;
use crate::introspective_calculus::inference::{Inference, ProvenInference};
use crate::introspective_calculus::{InferenceParser, RWMFormula};
use itertools::Itertools;
use std::collections::BTreeMap;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::sync::LazyLock;

#[derive(Clone, Debug)]
pub struct Rule {
    inference: Inference,
    argument_order: Vec<String>,
}
fn lines(file: &mut impl BufRead) -> impl Iterator<Item = String> + '_ {
    file.lines()
        .map(Result::unwrap)
        .filter(|l| !l.chars().all(char::is_whitespace) && !l.starts_with('#'))
}
pub static RULES: LazyLock<BTreeMap<String, Rule>> = LazyLock::new(|| {
    let parser = InferenceParser::new();
    let mut file = BufReader::new(File::open("./data/ic_intrinsic_rules.ic").unwrap());
    lines(&mut file)
        .map(|l| match parser.parse(&l) {
            Ok(a) => (a.name.clone(), Rule::new(a.to_rwm())),
            Err(e) => panic!("Got error `{e}` while parsing rule `{l}`"),
        })
        .collect()
});

impl Rule {
    fn new(inference: Inference) -> Rule {
        let free_variables = inference.free_metavariables();
        let num_variables = free_variables.len();
        let versions =
            free_variables
                .into_iter()
                .permutations(num_variables)
                .map(|argument_order| Rule {
                    inference: inference.clone(),
                    argument_order,
                });
        versions
            .min_by_key(|r| {
                r.inference
                    .tuple_equality_form()
                    .map(|side| side.formula().naive_size())
                    .iter()
                    .sum::<usize>()
            })
            .unwrap()
    }
    pub fn inference(&self) -> &Inference {
        &self.inference
    }
    pub fn argument_order(&self) -> &[String] {
        &self.argument_order
    }
    pub fn by_name(name: &str) -> &'static Rule {
        RULES.get(name).unwrap()
    }
    pub fn canonical_internalization(&self) -> RWMFormula {
        let [a, b] = self.inference.tuple_equality_form().map(|side| {
            side.formula()
                .metavariables_to_arguments(&self.argument_order)
        });
        ic!(a = b).to_rwm()
    }
    pub fn external_proof(&self) -> ProvenInference {
        // the type Rule guarantees that it only has the actual rules as constructible values, so we are allowed to use make_rule here
        ProvenInference::rule(self.clone())
    }
    pub fn internal_proof(&self) -> ProvenInference {
        if self.inference.premises.is_empty() && self.argument_order.is_empty() {
            // we are already an internal rule, so we can produce a proof using
            let [a, b] = self.inference.conclusion.as_eq_sides().unwrap();
            ProvenInference::derive_chain(
                "internalize_axiom",
                vec![self.external_proof()],
                &ic!((id = id) = ((a,) = (b,))).to_rwm(),
            )
            .unwrap()
        } else {
            // all external rules have their canonical form postulated, so we are allowed to use make_rule here
            ProvenInference::rule(Rule::new(Inference::new(
                vec![],
                self.canonical_internalization(),
            )))
        }
    }
}
