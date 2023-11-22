use crate::ic;
use crate::introspective_calculus::inference::ProvenInference;
use crate::introspective_calculus::{RWMFormula, Substitutions};
use std::iter::zip;

pub struct Claim {
    pub parameters: Vec<String>,
    pub sides: [RWMFormula; 2],
}

impl Claim {
    pub fn specialize(&self, to: &Claim) -> Result<ProvenInference, String> {
        let mut substitutions = Substitutions::new();
        for (mine, theirs) in zip(&self.sides, &to.sides) {
            mine.add_substitutions_to_become(theirs, &mut substitutions)?;
        }
        let mut extractor = ic!(id).to_rwm();
        for parameter in &self.parameters {
            // if there is no substitution stored, that's because the argument was ignored, so any formula will do
            let substitution = substitutions.remove(parameter).unwrap_or_default();
            extractor = ic!((fuse extractor) substitution).to_rwm();
        }
        // extractor = extractor.metavariables_to_arguments();

        // for substitution in substitutions {
        //     //if
        // }
        Err("unimplemented".to_string())
    }
}
