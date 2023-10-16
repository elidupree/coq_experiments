#![feature(lazy_cell)]

use clap::{arg, Parser};
use coc_rs::introspective_calculus::logic::TrueFormula;
use coc_rs::introspective_calculus::{all_axioms, AbstractionKind, Atom, Formula, FormulaValue};
use coc_rs::utils::{read_json_file, write_json_file};
use coc_rs::{ic, match_ic};
use html_node::{html, text, Node};
use quick_and_dirty_web_gui::{callback, callback_with};
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, LazyLock, Mutex};

struct Interface {
    file_path: String,
    theorems: Vec<TrueFormula>,
    focus: Option<usize>,
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
enum ParenthesisNeeds {
    AndChain,
    ApplyLHS,
    AbstractionBody,
    AllCompounds,
    Nothing,
}

impl Interface {
    fn formula_html(&self, formula: &Formula, parenthesis_needs: ParenthesisNeeds) -> Node {
        use ParenthesisNeeds::*;
        let mut parenthesize = false;
        let specific = match &formula.value {
            FormulaValue::Atom(a) => {
                html! {<span class="atom">{text!("{a}")}</span>}
            }
            FormulaValue::Apply(children) => {
                parenthesize = !matches!(parenthesis_needs, ApplyLHS | Nothing);
                let l = self.formula_html(&children[0], ApplyLHS);
                let r = self.formula_html(&children[1], AllCompounds);
                html! {<span class="apply">{l}{text!{" "}}{r}</span>}
            }
            FormulaValue::And(children) => {
                parenthesize = !matches!(parenthesis_needs, AndChain | Nothing);
                let l = self.formula_html(&children[0], AndChain);
                let r = self.formula_html(&children[1], AndChain);
                html! {<span class="union">{l}{text!{" & "}}{r}</span>}
            }
            FormulaValue::Equals(children) => {
                parenthesize = parenthesis_needs != Nothing;
                let l = self.formula_html(&children[0], AllCompounds);
                let r = self.formula_html(&children[1], AllCompounds);
                html! {<span class="union">{l}{text!{" = "}}{r}</span>}
            }
            FormulaValue::Implies(children) => {
                parenthesize = parenthesis_needs != Nothing;
                let l = self.formula_html(&children[0], AllCompounds);
                let r = self.formula_html(&children[1], AllCompounds);
                html! {<span class="implies">{l}{text!{" → "}}{r}</span>}
            }
            FormulaValue::NamedGlobal { name, .. } => {
                html! {<span class="named_global">{text!("{name}")}</span>}
            }
            FormulaValue::Metavariable(name) => {
                html! {<span class="metavariable">{text!("{name}")}</span>}
            }
            FormulaValue::NameAbstraction(kind, name, body) => {
                parenthesize = !matches!(parenthesis_needs, AbstractionBody | Nothing);
                let b = self.formula_html(body, AbstractionBody);
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
        let formula = formula.clone();
        html! {
            <span class="subformula" onclick={
                interface_callback(move |i| {i.click_formula(&formula);})
            }>
                {body}
            </span>
        }
    }
    fn inference_html(
        &self,
        index: usize,
        existing_inferences: &HashMap<Formula, usize>,
        axioms: &HashSet<Formula>,
    ) -> Node {
        let theorem = &self.theorems[index];
        let formula = theorem.formula();
        let mut buttons = vec![
            html! {<button onclick={
                interface_callback(move |i| {i.theorems.remove(index);})
            }>X</button>},
            html! {<button onclick={
                interface_callback(move |i| {i.theorems.push(i.theorems[index].clone());})
            }>Copy</button>},
        ];
        // match_ic!(formula, {
        //     //TODO reduce duplicate code ID 3894475843
        //     ((equals a) b) => {
        //         if let Some(a) = existing_inferences.get(a) {
        //             let b = b.clone();
        //             buttons.push(html! {<button onclick={
        //                 interface_callback(move |i| {i.inferences[index] = TrueFormula::substitute_whole_formula(theorem, a).unwrap();})
        //             }>Proceed to consequent</button>});
        //         }
        //     }
        // });
        // match_ic!(formula, {
        //     ((and a) b) => {
        //         let a = a.clone();
        //         let b = b.clone();
        //         buttons.push(html! {<button onclick={
        //             interface_callback(move |i| {i.theorems[index].formula = a.clone();})
        //         }>Use left</button>});
        //         buttons.push(html! {<button onclick={
        //             interface_callback(move |i| {i.theorems[index].formula = b.clone();})
        //         }>Use right</button>});
        //     },
        //     (all a) => {
        //         let a = a.clone();
        //         buttons.push(html! {<button onclick={
        //             interface_callback(move |i| {
        //                 let rule = a.clone();
        //                 i.theorems[index].formula = ic!(rule empty_set);
        //             })
        //         }>Specialize</button>});
        //     },
        // });
        // let mut unfolded = formula.clone();
        // if unfolded.unfold_left(2) {
        //     buttons.push(html! {<button onclick={
        //         interface_callback(move |i| {i.theorems[index].formula = unfolded.clone()})
        //     }>Unfold</button>});
        //     buttons.push(html! {<button onclick={
        //         interface_callback(move |i| {
        //             for _ in 0..100 {
        //                 if !i.theorems[index].formula.unfold_left(2) {
        //                     break
        //                 }
        //             }
        //         })
        //     }>Unfold+</button>});
        // }
        let (name, formula) = match &formula.value {
            FormulaValue::NamedGlobal { name, value } => (&**name, value),
            _ => ("", formula),
        };
        html! {
            <div class="inference-name">
                {text!("{}: ", name)}
            </div>
            <div class="inference-body">
                {self.formula_html(formula, ParenthesisNeeds::Nothing)}
            </div>
            <div class="inference-buttons">
                {buttons}
            </div>
        }
    }
    fn whole_page(&self) -> Node {
        let existing_inferences = self
            .theorems
            .iter()
            .enumerate()
            .map(|(i, t)| (t.formula().clone(), i))
            .collect();
        let axioms = all_axioms()
            .into_iter()
            .map(|t| t.formula().clone())
            .collect();
        let inferences =
            self.theorems.iter().enumerate().map(|(index, _inference)| {
                self.inference_html(index, &existing_inferences, &axioms)
            });
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
    let inferences =
        read_json_file::<_, Vec<TrueFormula>>(&args.file_path).unwrap_or_else(|_| all_axioms());
    Mutex::new(Interface {
        file_path: args.file_path,
        theorems: inferences,
        focus: None,
    })
});

fn with_interface(f: impl FnOnce(&mut Interface)) {
    let mut interface = INTERFACE.lock().unwrap();
    f(&mut *interface);
    //interface.optimize_positions();
    interface.update_gui();
    write_json_file(&interface.file_path, &interface.theorems).unwrap();
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
