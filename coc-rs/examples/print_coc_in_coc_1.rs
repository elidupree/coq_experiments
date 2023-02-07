use coc_rs::coc_text_format_1::Document;
use coc_rs::constructors::COC;

fn main() {
    print!("{}", Document::from_constructors(&*COC));
}
