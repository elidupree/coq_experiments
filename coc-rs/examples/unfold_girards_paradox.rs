use coc_rs::coc_text_format_1::Document;

fn main() {
    let globals = Document::parse(&std::fs::read_to_string("data/girards_paradox.coc_1").unwrap())
        .into_globals();

    let mut running_paradox = globals.definitions.get("Paradox").unwrap().clone();
    for step in 0..10 {
        println!("{step}: {running_paradox}");
        let mut ty = running_paradox.naive_type(&globals, Default::default());
        println!(" : {}", ty);
        while let Some(crease) = ty.favored_crease_in_closed_formula(&globals, Default::default()) {
            ty.unfold(&crease, &globals).unwrap();
            println!(" : {}", ty);
        }
        let crease = running_paradox
            .favored_crease_in_closed_formula(&globals, Default::default())
            .unwrap();
        running_paradox.unfold(&crease, &globals).unwrap();
    }
}
