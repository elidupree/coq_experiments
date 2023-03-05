use coc_rs::coc_text_format_1::{Document, Formula};
use colored::Colorize;

fn on_left_spine(f: &Formula, g: &str) -> bool {
    match f {
        Formula::Usage(n) => &**n == g,
        Formula::Apply(children) => on_left_spine(&children[0], g),
        _ => false,
    }
}

fn main() {
    let globals = Document::parse(&std::fs::read_to_string("data/girards_paradox.coc_1").unwrap())
        .into_globals();

    let mut running_paradox = globals.definitions.get("Paradox").unwrap().clone();
    for step in 0..30 {
        // if on_left_spine(&running_paradox, "P2") {
        println!("{step}: {running_paradox}");
        // }
        // let mut ty = running_paradox.naive_type(&globals, Default::default());
        // println!(" : {}", ty);
        // while let Some(crease) = ty.favored_crease_in_closed_formula(&globals, Default::default()) {
        //     ty.unfold(&crease, &globals).unwrap();
        //     println!(" : {}", ty);
        // }
        println!("{}", running_paradox.to_string().len());
        let crease = running_paradox
            .favored_crease_in_closed_formula(&globals, Default::default())
            .unwrap();
        let redex = running_paradox.subformula(&crease).clone();
        running_paradox.unfold(&crease, &globals).unwrap();
        let contractum = running_paradox.subformula(&crease);
        println!(
            "- {}\n+ {}",
            redex.to_string().red(),
            contractum.to_string().green()
        );
    }
}
