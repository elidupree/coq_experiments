#![feature(lazy_cell)]

use clap::{arg, Parser};
use coc_rs::introspective_calculus::Formula;
use coc_rs::utils::{read_json_file, write_json_file};
use quick_and_dirty_web_gui::{callback, callback_with};
use std::sync::{LazyLock, Mutex};

struct Interface {
    file_path: String,
    inferences: Vec<Formula>,
    focus: Option<usize>,
}

impl Interface {
    fn whole_page(&self) -> String {
        // let nodes = self.nodes();
        // let new_buttons = COC.types.keys().cloned().map(|typename| {
        //     let text = text!(&typename);
        //     html! {
        //         <div class="new_metavariable">
        //             <button onclick={callback(move || new_global(typename.clone()))}>
        //                 {text}
        //             </button>
        //         </div> : String
        //     }
        // });
        // html! {
        //     <div class="page">
        //         <div class="new_metavariables">
        //             {new_buttons}
        //         </div>
        //         {nodes}
        //         <div style="clear: both"></div>
        //     </div>
        // }
        "".into()
    }

    fn update_gui(&self) {
        quick_and_dirty_web_gui::replace_html(self.whole_page().to_string());
    }
}

static INTERFACE: LazyLock<Mutex<Interface>> = LazyLock::new(|| {
    let args = Args::parse();
    let inferences =
        read_json_file::<_, Vec<Formula>>(&args.file_path).unwrap_or_else(|_| Vec::default());
    Mutex::new(Interface {
        file_path: args.file_path,
        inferences,
        focus: None,
    })
});

fn with_interface(f: impl FnOnce(&mut Interface)) {
    let mut interface = INTERFACE.lock().unwrap();
    f(&mut *interface);
    //interface.optimize_positions();
    interface.update_gui();
    write_json_file(&interface.file_path, &interface.inferences).unwrap();
}

// fn unfocus() {
//     with_interface(|interface: &mut Interface| {
//         interface.focus = None;
//     });
// }

// fn set_focus(focus: usize) {
//     with_interface(|interface: &mut Interface| {
//         interface.focus = Some (usize);
//     });
// }

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to data file
    #[arg(short, long)]
    file_path: String,

    /// .coc_1 file to inject
    #[arg(short, long)]
    inject_coc_1: Option<String>,
}

#[actix_web::main]
async fn main() {
    with_interface(|_| {});
    // actix_web::rt::spawn(async {
    //     loop {
    //         actix_web::rt::time::sleep(Duration::from_millis(1000)).await;
    //         with_interface(|_| {});
    //     }
    // });
    quick_and_dirty_web_gui::launch("./static/ic_explorer.html", 4987).await;
}
