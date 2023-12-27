use crate::introspective_calculus::inference::Inference;
use crate::introspective_calculus::proof_hierarchy::{Proof, ProofDerivation};
use crate::introspective_calculus::provers::{ByAssumingIt, BySpecializingAnyCoreRule};
use crate::introspective_calculus::solver_pool::Goal;
use crate::introspective_calculus::InferenceParser;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::error::Error;
use std::fs::File;
use std::io;
use std::io::{BufRead, BufReader};
use std::path::Path;

#[derive(Default)]
pub struct ProofBucket {
    pub proofs: HashMap<Goal, Proof>,
}

#[derive(Serialize, Deserialize)]
struct SavedProofLine(String, Vec<String>);

impl Proof {
    pub fn to_goal(&self) -> Goal {
        Goal {
            premises: self.premises().iter().cloned().collect(),
            conclusion: self.conclusion(),
        }
    }
}
impl Inference {
    pub fn to_goal(&self) -> Goal {
        Goal {
            premises: self.premises.iter().cloned().collect(),
            conclusion: self.conclusion.clone(),
        }
    }
}

impl ProofBucket {
    pub fn add(&mut self, proof: &Proof, writer: &mut dyn io::Write) {
        let goal = proof.to_goal();
        if !self.proofs.contains_key(&goal) {
            // no need to save premises, they are "obvious"
            if let ProofDerivation::Rule(p) = proof.derivation() {
                let dependencies: Vec<Goal> = p
                    .premise_proofs
                    .iter()
                    .map(|premise_proof| {
                        self.add(premise_proof, writer);
                        premise_proof.to_goal()
                    })
                    .collect();

                let line = SavedProofLine(
                    goal.to_string(),
                    dependencies.iter().map(ToString::to_string).collect(),
                );
                // note: at this point it's theoretically possible that a messy proof used itself as a premise, which would mean there is already an entry. if that's true then we don't want to overwrite it with the current one, or write to the savefile.
                self.proofs.entry(goal).or_insert_with(|| {
                    serde_json::to_writer(writer, &line).unwrap();
                    proof.clone()
                });
            }
        }
    }

    pub fn get_proof(&self, goal: &Goal) -> Option<&Proof> {
        self.proofs.get(goal)
    }

    pub fn reconstruct_proof(&self, goal: &Goal, dependencies: &[Goal]) -> Option<Proof> {
        if goal.premises.len() == 1 && goal.premises.iter().next().unwrap() == &goal.conclusion {
            return Some(goal.conclusion.prove(ByAssumingIt));
        }

        let mut premise_proofs = Vec::new();
        for dependency in dependencies {
            premise_proofs.push(self.get_proof(dependency)?.clone());
        }
        goal.conclusion
            .try_prove(BySpecializingAnyCoreRule {
                premise_proofs: &premise_proofs,
            })
            .ok()
    }

    pub fn load_line<E: Error + Send + Sync + 'static>(
        &mut self,
        line: Result<String, E>,
    ) -> Option<()> {
        let parser = InferenceParser::new();
        let SavedProofLine(g, d) = serde_json::from_str(&line.ok()?).ok()?;
        let goal = parser.parse(&g).ok()?.to_rwm().to_goal();
        let dependencies = d
            .iter()
            .map(|d| parser.parse(d).ok().map(|p| p.to_rwm().to_goal()))
            .collect::<Option<Vec<_>>>()?;
        let proof = self.reconstruct_proof(&goal, &dependencies)?;
        self.proofs.insert(goal, proof);
        Some(())
    }

    pub fn load<E: Error + Send + Sync + 'static>(
        lines: impl Iterator<Item = Result<String, E>>,
    ) -> ProofBucket {
        let mut result = ProofBucket::default();
        for line in lines {
            let _ = result.load_line(line);
        }
        result
    }

    pub fn load_file(path: &Path) -> Result<ProofBucket, anyhow::Error> {
        Ok(Self::load(BufReader::new(File::open(path)?).lines()))
    }
}
