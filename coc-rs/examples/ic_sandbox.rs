use coc_rs::introspective_calculus;

fn main() {
    for axiom in introspective_calculus::all_axioms() {
        println!(
            "{}: {}",
            axiom.formula(),
            axiom.as_raw_with_metavariables().as_shorthand()
        );
    }
}
