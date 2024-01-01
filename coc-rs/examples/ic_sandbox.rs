use coc_rs::introspective_calculus::proof_hierarchy::{InferenceAsEquivalence, Proof};
use coc_rs::introspective_calculus::provers::{
    ByAssumingIt, BySpecializingAxiom, BySpecializingWithPremises, ByUnfolding,
};
use coc_rs::introspective_calculus::raw_proofs::{Axiom, CleanExternalRule, Rule, RuleTrait};
use coc_rs::introspective_calculus::raw_proofs_ext::ALL_AXIOM_SCHEMAS;
use coc_rs::introspective_calculus::solver_pool::GLOBAL_SOLVER;
use coc_rs::{formula, inf};
use hash_capsule::serialization::deserialize_file_with_hash_capsules;
use itertools::Itertools;
use std::time::Instant;

fn main() {
    if let Ok(known_proofs_iter) =
        deserialize_file_with_hash_capsules::<Proof>("./data/cached_proofs")
    {
        let mut known_proofs: Vec<Proof> = known_proofs_iter
            // .filter_map(Result::ok)
            .map(Result::unwrap)
            .collect();
        dbg!(known_proofs.len());
        for proof in &known_proofs {
            GLOBAL_SOLVER
                .lock()
                .unwrap()
                .discover_proof(proof.clone(), true);
        }
        known_proofs.sort_by_key(|p| dbg!(p.naive_size()));
        let start = Instant::now();
        for proof in &known_proofs {
            let start2 = Instant::now();
            dbg!(proof.to_goal());
            dbg!(proof.naive_size());
            dbg!(start2.elapsed(), start.elapsed());
            let internal_implication = proof
                .premises_to_internal_implication(&proof.premises().iter().cloned().collect_vec());
            dbg!(proof.to_goal());
            dbg!(internal_implication.proof().naive_size());
            dbg!(start2.elapsed(), start.elapsed());
            let fully_internal = internal_implication
                .proof()
                .variables_to_internalized_argument_list(
                    &internal_implication
                        .proof()
                        .to_goal()
                        .in_arbitrary_order()
                        .free_metavariables()
                        .into_iter()
                        .collect_vec(),
                );
            dbg!(proof.to_goal());
            dbg!(fully_internal.proof().naive_size());
            dbg!(start2.elapsed(), start.elapsed());
            let raw = fully_internal.proof().to_raw();
            dbg!(proof.to_goal());
            dbg!(start2.elapsed(), start.elapsed());
        }
    }

    let a = formula!("(l=>((const A) l = (const B) l)) = (l=>((const C) l = (const D) l))")
        .prove(ByAssumingIt);
    formula!("(l=>(((const A) l,(const E) l)=((const B) l,(const F) l))) = (l=>(((const C) l,(const E) l)=((const D) l,(const F) l)))").to_rwm().prove(BySpecializingWithPremises{proof_to_specialize: &Rule::from(CleanExternalRule::SubstituteInConjunction).to_proof(), premise_proofs: &[a] });

    let inf = CleanExternalRule::SubstituteInRhs.inference();
    dbg!(&inf);
    let infeq = InferenceAsEquivalence::from_inference(inf);
    dbg!(&infeq.formula());
    let a = Axiom::new(infeq.formula().clone());
    eprintln!("{}", a.internal_form);
    let b = a
        .internal_form
        .args_to_return(&formula!("(A=B) ->((x=>x C)A = (x=>x C)B)").to_rwm());
    dbg!(b);

    eprintln!("a");
    (&*ALL_AXIOM_SCHEMAS);

    eprintln!("b");
    let f = formula!("fuse A B C D = (A C) (B C) D")
        .prove(ByUnfolding)
        .variables_to_internalized_argument_list(
            &"ABCD".chars().map(|c| c.to_string()).collect_vec(),
        );
    //eprintln!("{}", f.formula().formula());
    eprintln!("{}", f.formula().sides[0]);
    eprintln!("{}", f.formula().sides[1]);
}
