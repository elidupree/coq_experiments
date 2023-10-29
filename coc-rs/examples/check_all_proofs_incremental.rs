use coc_rs::introspective_calculus::derivers::{
    IncrementalDeriverWorkResult, SearchManyEnvironment,
};
use coc_rs::introspective_calculus::inference::load_proof;
use std::path::Path;

fn main() {
    let mut environment = SearchManyEnvironment::new();

    for entry in std::fs::read_dir("./data/ic_proofs").unwrap() {
        let path = entry.unwrap().path();
        if let Ok(proof) = load_proof(path) {
            environment.add_written_proof(&proof);
        }
    }
    let mut steps = 0;

    loop {
        match environment.do_some_work() {
            IncrementalDeriverWorkResult::NothingToDoRightNow => {
                println!("No more work to do ({steps} steps total)");
                return;
            }
            IncrementalDeriverWorkResult::StillWorking => {
                steps += 1;
            }
            IncrementalDeriverWorkResult::DiscoveredInference(inference) => {
                println!("Completed {inference}");
            }
        }
    }
}
