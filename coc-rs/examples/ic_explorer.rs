#![feature(lazy_cell)]

use clap::{arg, Parser};
use coc_rs::introspective_calculus::{
    all_official_rules, AbstractionKind, Atom, ExplicitRule, Formula,
};
use coc_rs::utils::{read_json_file, write_json_file};
use coc_rs::{ic, match_ic};
use html_node::{html, text, Node};
use quick_and_dirty_web_gui::{callback, callback_with};
use std::sync::{Arc, LazyLock, Mutex};

struct Interface {
    file_path: String,
    inferences: Vec<ExplicitRule>,
    focus: Option<usize>,
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
enum ParenthesisNeeds {
    UnionChain,
    ApplyLHS,
    AbstractionBody,
    AllCompounds,
    Nothing,
}

impl Interface {
    fn formula_html(&self, formula: Formula, parenthesis_needs: ParenthesisNeeds) -> Node {
        use ParenthesisNeeds::*;
        let mut parenthesize = false;
        let specific = match &formula {
            Formula::Atom(a) => {
                html! {<span class="atom">{text!("{a}")}</span>}
            }
            Formula::Apply(children) => {
                parenthesize = !matches!(parenthesis_needs, ApplyLHS | Nothing);
                let l = self.formula_html(children[0].clone(), ApplyLHS);
                let r = self.formula_html(children[1].clone(), AllCompounds);
                html! {<span class="apply">{l}{text!{" "}}{r}</span>}
            }
            Formula::Implies(children) => {
                parenthesize = parenthesis_needs != Nothing;
                let l = self.formula_html(children[0].clone(), AllCompounds);
                let r = self.formula_html(children[1].clone(), AllCompounds);
                html! {<span class="implies">{l}{text!{" → "}}{r}</span>}
            }
            Formula::Union(children) => {
                parenthesize = !matches!(parenthesis_needs, UnionChain | Nothing);
                let l = self.formula_html(children[0].clone(), UnionChain);
                let r = self.formula_html(children[1].clone(), UnionChain);
                html! {<span class="union">{l}{text!{" ∪ "}}{r}</span>}
            }
            Formula::Id => {
                html! {<span class="technically_not_atom">{text!("id")}</span>}
            }
            Formula::EmptySet => {
                html! {<span class="technically_not_atom">{text!("∅")}</span>}
            }
            Formula::Metavariable(name) => {
                html! {<span class="metavariable">{text!("{name}")}</span>}
            }
            Formula::NameAbstraction(kind, name, body) => {
                parenthesize = !matches!(parenthesis_needs, AbstractionBody | Nothing);
                let b = self.formula_html((**body).clone(), AbstractionBody);
                match kind {
                    AbstractionKind::Lambda => {
                        html! {<span class="abstraction lambda">{text!("{name} => ")}{b}</span>}
                    }
                    AbstractionKind::ForAll => {
                        html! {<span class="abstraction forall">{text!("∀{name}, ")}{b}</span>}
                    }
                }
            }
        };
        let body = if parenthesize {
            vec![text!("("), specific, text!(")")]
        } else {
            vec![specific]
        };
        html! {
            <span class="subformula" onclick={
                interface_callback(move |i| {i.click_formula(&formula);})
            }>
                {body}
            </span>
        }
    }
    fn inference_html(&self, index: usize) -> Node {
        let rule = &self.inferences[index];
        let formula = &rule.formula;
        let mut buttons = vec![
            html! {<button onclick={
                interface_callback(move |i| {i.inferences.remove(index);})
            }>X</button>},
            html! {<button onclick={
                interface_callback(move |i| {i.inferences.push(i.inferences[index].clone());})
            }>Copy</button>},
        ];
        // match_ic!(formula, {
        //     ((implies empty_set) a) => {
        //         let a = a.clone();
        //         buttons.push(html! {<button onclick={
        //             interface_callback(move |i| {i.inferences[index].formula = a.clone();})
        //         }>To inference</button>});
        //     }
        // });
        match_ic!(formula, {
            ((union a) b) => {
                let a = a.clone();
                buttons.push(html! {<button onclick={
                    interface_callback(move |i| {i.inferences[index].formula = a.clone();})
                }>To inference</button>});
            },
            (all a) => {
                buttons.push(html! {<button onclick={
                    interface_callback(move |i| {
                        let Formula::Apply(a) = &i.inferences[index].formula else { return };
                        let rule = a[1].clone();
                        i.inferences[index].formula = ic!(rule empty_set);
                    })
                }>Specialize</button>});
            },
        });
        let mut unfolded = formula.clone();
        if unfolded.unfold_left() {
            buttons.push(html! {<button onclick={
                interface_callback(move |i| {i.inferences[index].formula = unfolded.clone()})
            }>Unfold</button>});
            buttons.push(html! {<button onclick={
                interface_callback(move |i| {
                    for _ in 0..100 {
                        if !i.inferences[index].formula.unfold_left() {
                            break
                        }
                    }
                })
            }>Unfold+</button>});
        }
        html! {
            <div class="inference-name">
                {text!("{}: ", rule.name)}
            </div>
            <div class="inference-body">
                {self.formula_html(formula.prettify('a'), ParenthesisNeeds::Nothing)}
            </div>
            <div class="inference-buttons">
                {buttons}
            </div>
        }
    }
    fn whole_page(&self) -> Node {
        let inferences = self
            .inferences
            .iter()
            .enumerate()
            .map(|(index, _inference)| self.inference_html(index));
        html! {
            <div class="inferences">
                {inferences}
                <div style="clear: both"></div>
            </div>
        }
    }

    fn click_formula(&mut self, formula: &Formula) {}

    fn update_gui(&self) {
        quick_and_dirty_web_gui::replace_html(self.whole_page().to_string());
    }
}

static INTERFACE: LazyLock<Mutex<Interface>> = LazyLock::new(|| {
    let args = Args::parse();
    let inferences = read_json_file::<_, Vec<ExplicitRule>>(&args.file_path)
        .unwrap_or_else(|_| all_official_rules());
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

fn interface_callback(mut f: impl FnMut(&mut Interface) + Send + 'static) -> String {
    callback(move || with_interface(|i| f(i)))
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
