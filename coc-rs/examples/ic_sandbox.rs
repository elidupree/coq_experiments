use coc_rs::formula;
use coc_rs::introspective_calculus::provers::ByUnfolding;
use coc_rs::introspective_calculus::raw_proofs_ext::ALL_AXIOM_SCHEMAS;
use itertools::Itertools;

fn main() {
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
