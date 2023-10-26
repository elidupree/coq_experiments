use coc_rs::introspective_calculus::proofs::get_deriver_by_name;

fn main() {
    for entry in std::fs::read_dir("./data/ic_proofs").unwrap() {
        let path = entry.unwrap().path();
        get_deriver_by_name(path.file_name().unwrap().to_str().unwrap());
    }
}
