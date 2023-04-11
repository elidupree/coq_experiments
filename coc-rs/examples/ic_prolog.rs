use coc_rs::introspective_calculus::prolog;
use std::fs;

fn main() {
    let path = std::env::args().collect::<Vec<_>>()[1].clone();
    fs::write(path, prolog::knowledge_base("data/ic_ordinary_axioms.ic")).unwrap();
}
