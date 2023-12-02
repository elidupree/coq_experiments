use crate::introspective_calculus::raw_proofs::RawProof;

impl RawProof {
    pub fn substitute_in_conclusion(&self, equivalence: RawProof) -> Option<RawProof> {
        let [a, b] = equivalence.conclusion().as_eq_sides().unwrap();
        if self.conclusion() == a {
            Some(RawProof::new())
        }
    }
}
