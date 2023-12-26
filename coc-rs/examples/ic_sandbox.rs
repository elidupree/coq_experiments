use coc_rs::introspective_calculus::proof_hierarchy::InferenceAsEquivalence;
use coc_rs::introspective_calculus::provers::{
    ByAssumingIt, BySpecializingAxiom, BySpecializingWithPremises, ByUnfolding,
};
use coc_rs::introspective_calculus::raw_proofs::{Axiom, CleanExternalRule, Rule, RuleTrait};
use coc_rs::introspective_calculus::raw_proofs_ext::ALL_AXIOM_SCHEMAS;
use coc_rs::{formula, inf};
use itertools::Itertools;

fn main() {
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
