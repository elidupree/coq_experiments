use coc_rs::introspective_calculus;

fn main() {
    for axiom in introspective_calculus::all_axioms("data/ic_ordinary_axioms.ic") {
        println!(
            "{}",
            axiom.conclusion.to_raw_with_metavariables().as_shorthand()
        );
    }
}
