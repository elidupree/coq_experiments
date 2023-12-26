use coc_rs::formula;
use coc_rs::introspective_calculus::proof_hierarchy::InferenceAsEquivalence;
use coc_rs::introspective_calculus::provers::ByUnfolding;
use coc_rs::introspective_calculus::raw_proofs::{Axiom, CleanExternalRule, RuleTrait};
use coc_rs::introspective_calculus::raw_proofs_ext::ALL_AXIOM_SCHEMAS;
use itertools::Itertools;

fn main() {
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
