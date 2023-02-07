use coc_rs::coc_text_format_1::Document;
use std::env::args;

fn main() {
    let path = args().collect::<Vec<_>>()[1].clone();
    let text = std::fs::read_to_string(&path).unwrap();
    let formatted = Document::reformat(&text);
    if *text == *formatted {
        println!("Already formatted!");
    } else {
        std::fs::write(&path, formatted.as_bytes()).unwrap();
        println!("Changes made!");
    }
}
