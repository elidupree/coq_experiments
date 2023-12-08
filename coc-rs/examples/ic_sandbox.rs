use coc_rs::formula;
use coc_rs::introspective_calculus::provers::ByUnfolding;
use coc_rs::introspective_calculus::raw_proofs_ext::ALL_AXIOM_SCHEMAS;
use itertools::Itertools;

fn main() {
    (&*ALL_AXIOM_SCHEMAS);

    formula!("fuse A B C D = (A C) (B C) D")
        .prove(ByUnfolding)
        .to_uncurried_function_equivalence(&"ABCD".chars().map(|c| c.to_string()).collect_vec());
}
