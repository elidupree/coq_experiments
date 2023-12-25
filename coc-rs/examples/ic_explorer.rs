#![feature(lazy_cell)]

use clap::{arg, Parser};
// use coc_rs::introspective_calculus::derivers::{
//     IncrementalDeriverWorkResult, PrettyLine, SearchManyEnvironment,
// };
use coc_rs::introspective_calculus::inference::{load_proof, ProofScript};
use coc_rs::introspective_calculus::{
    all_axioms, AbstractionKind, Formula, FormulaParser, FormulaValue, RWMFormula,
};
// use coc_rs::utils::{read_json_file, write_json_file};
use ai_framework::time_sharing::WorkResult;
use coc_rs::introspective_calculus::solver_pool::{Goal, ALL_PROOF_SCRIPTS, GLOBAL_SOLVER};
use html_node::{html, text, Node};
use quick_and_dirty_web_gui::{callback, callback_with};
use serde::de::DeserializeOwned;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::{LazyLock, Mutex};
use std::time::{Duration, Instant};

struct Interface {
    file_path: String,
    theorems: Vec<Formula>,
    focus: Option<usize>,
    sandbox_text: String,
    sandbox_message: String,
    proof_order: Vec<String>,
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
enum ParenthesisNeeds {
    AndLHS,
    ApplyLHS,
    AbstractionBody,
    AllCompounds,
    Nothing,
}

impl Interface {
    fn formula_html(&self, formula: &Formula, parenthesis_needs: ParenthesisNeeds) -> Node {
        use ParenthesisNeeds::*;
        let mut parenthesize = false;
        let specific = match formula.value() {
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
                parenthesize = !matches!(parenthesis_needs, AndLHS | Nothing);
                let l = self.formula_html(&children[0], AndLHS);
                let r = self.formula_html(&children[1], AllCompounds);
                html! {<span class="and">{l}{text!{" & "}}{r}</span>}
            }
            FormulaValue::Equals(children) => {
                parenthesize = parenthesis_needs != Nothing;
                let l = self.formula_html(&children[0], AllCompounds);
                let r = self.formula_html(&children[1], AllCompounds);
                html! {<span class="equals">{l}{text!{" = "}}{r}</span>}
            }
            FormulaValue::Implies(children) => {
                parenthesize = parenthesis_needs != Nothing;
                let l = self.formula_html(&children[0], AllCompounds);
                let r = self.formula_html(&children[1], AllCompounds);
                html! {<span class="implies">{l}{text!{" → "}}{r}</span>}
            }
            FormulaValue::Tuple(children) => {
                parenthesize = parenthesis_needs != Nothing;
                let mut results: Vec<Node> = Vec::new();
                if let Some((first, rest)) = children.split_first() {
                    results.push(self.formula_html(first, AllCompounds));
                    for f in rest {
                        results.push(text! {", "});
                        results.push(self.formula_html(f, AllCompounds));
                    }
                }
                html! {<span class="tuple">{results}</span>}
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
    fn theorem_html(
        &self,
        index: usize,
        existing_theorems: &HashMap<Formula, usize>,
        axioms: &HashSet<Formula>,
    ) -> Node {
        let theorem = &self.theorems[index];
        let formula = theorem;
        let mut buttons = vec![
            html! {<button onclick={
                interface_callback(move |i| {i.theorems.remove(index);})
            }>X</button>},
            html! {<button onclick={
                interface_callback(move |i| {i.theorems.push(i.theorems[index].clone());})
            }>Copy</button>},
        ];
        // match_ic!(formula, {
        //     //TODO use eq_sides instead
        //     ((equals a) b) => {
        //         if let Some(a) = existing_theorems.get(a) {
        //             let b = b.clone();
        //             buttons.push(html! {<button onclick={
        //                 interface_callback(move |i| {i.theorems[index] = TrueFormula::substitute_whole_formula(theorem, a).unwrap();})
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
        let (name, formula) = match formula.value() {
            FormulaValue::NamedGlobal { name, value } => (&**name, value),
            _ => ("", formula),
        };
        html! {
            <div class="theorem-name">
                {text!("{}: ", name)}
            </div>
            <div class="theorem-body">
                {self.formula_html(formula, ParenthesisNeeds::Nothing)}
            </div>
            <div class="theorem-buttons">
                {buttons}
            </div>
        }
    }
    fn sandbox(&self) -> Node {
        let callback = interface_callback_with(
            r#"document.getElementById("sandbox_text").value"#,
            move |text: String, i| {
                i.sandbox_text = text;
                match FormulaParser::new().parse(&i.sandbox_text) {
                    Ok(formula) => {
                        let mut formula = formula.to_rwm();
                        formula.unfold_until(100);
                        let new = formula.to_string();
                        if new == i.sandbox_text {
                            i.sandbox_message = "Nothing to do".to_string();
                        } else {
                            i.sandbox_message = "Unfolded!".to_string();
                        }
                        i.sandbox_text = formula.to_string();
                    }
                    Err(e) => {
                        i.sandbox_message = e.to_string();
                    }
                }
            },
        );
        html! {
            <div class="sandbox">
                <textarea id="sandbox_text">{text!("{}", self.sandbox_text)}</textarea>
                <button onclick={
                    callback
                }>Unfold</button>
                <div>{text!("{}", self.sandbox_message)}</div>
            </div>
        }
    }

    fn proof_script_html(&self, name: &str, script: &ProofScript) -> Node {
        let premises: BTreeSet<RWMFormula> = script.premises.iter().map(Formula::to_rwm).collect();
        let lines = script.conclusions.iter().map(|line| {
            let classes = if GLOBAL_SOLVER
                .lock()
                .unwrap()
                .get_existing_proof(&Goal {
                    premises: premises.clone(),
                    conclusion: line.to_rwm(),
                })
                .is_some()
            {
                "proof_line proven"
            } else {
                "proof_line"
            };
            html! {
                <div class={classes}>
                    // <div class="proof_line_name">
                    //     {text!("{}", line.name)}
                    // </div>
                    <div class="proof_line_formula">
                        {self.formula_html(line, ParenthesisNeeds::Nothing)}
                    </div>
                    <div class="proof_line_raw_formula">
                        {self.formula_html(&line.to_rwm().into(), ParenthesisNeeds::Nothing)}
                    </div>
                </div>
            }
        });
        html! {
            <div class="proof_script">
                <div class="partial_proof_name">{text!("{}", name)}</div>
                {lines}
            </div>
        }
    }

    fn whole_page(&self) -> Node {
        let existing_theorems = self
            .theorems
            .iter()
            .enumerate()
            .map(|(i, t)| (t.clone(), i))
            .collect();
        let axioms = all_axioms().into_iter().collect();
        let theorems = self
            .theorems
            .iter()
            .enumerate()
            .map(|(index, _theorem)| self.theorem_html(index, &existing_theorems, &axioms));
        let proof_scripts = self
            .proof_order
            .iter()
            .map(|s| (s, ALL_PROOF_SCRIPTS.get(s).unwrap()))
            .map(|(name, script)| self.proof_script_html(name, script));
        html! {
            <div class="page">
                <div class="theorems">
                    {theorems}
                    <div style="clear: both"></div>
                </div>
                {self.sandbox()}
                {proof_scripts}
            </div>
        }
    }

    fn click_formula(&mut self, _formula: &Formula) {}

    fn update_gui(&self) {
        quick_and_dirty_web_gui::replace_html(self.whole_page().to_string());
    }
}

static INTERFACE: LazyLock<Mutex<Interface>> = LazyLock::new(|| {
    let args = Args::parse();
    // let mut theorems = read_json_file::<_, Vec<Formula>>(&args.file_path).unwrap_or_default();
    let mut theorems: Vec<Formula> = Vec::new();
    for axiom in all_axioms() {
        if !theorems.contains(&axiom) {
            theorems.push(axiom);
        }
    }
    let mut proof_order = Vec::new();
    for entry in std::fs::read_dir("./data/ic_proofs").unwrap() {
        let path = entry.unwrap().path();
        let name = path.file_name().unwrap().to_str().unwrap();
        let modified = std::fs::metadata(&path).unwrap().modified().unwrap();
        match load_proof(&path) {
            Ok(proof) => {
                println!("loaded {path:?}");
                proof_order.push((name.to_string(), modified));
            }
            Err(e) => {
                println!("failed to load {path:?}: {e}");
            }
        }
    }
    proof_order.sort_by_key(|(_name, time)| *time);
    let proof_order = proof_order
        .into_iter()
        .rev()
        .map(|(name, _time)| name)
        .collect();
    Mutex::new(Interface {
        file_path: args.file_path,
        theorems: theorems,
        focus: None,
        sandbox_text: "".to_string(),
        sandbox_message: "".to_string(),
        proof_order,
    })
});

fn with_interface(f: impl FnOnce(&mut Interface)) {
    let mut interface = INTERFACE.lock().unwrap();
    f(&mut *interface);
    //interface.optimize_positions();
    let start = Instant::now();
    interface.update_gui();
    let elapsed = start.elapsed();
    if elapsed > Duration::from_millis(10) {
        eprintln!("UI update took a while: {elapsed:?}");
    }
    //write_json_file(&interface.file_path, &interface.theorems).unwrap();
}

fn interface_callback(mut f: impl FnMut(&mut Interface) + Send + 'static) -> String {
    callback(move || with_interface(|i| f(i)))
}
fn interface_callback_with<D: DeserializeOwned>(
    js: &str,
    mut f: impl FnMut(D, &mut Interface) + Send + 'static,
) -> String {
    callback_with(js, move |d| with_interface(|i| f(d, i)))
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
    actix_web::rt::spawn(async {
        let mut done = false;
        while !done {
            let mut steps = 0;
            with_interface(|interface| {
                let start = Instant::now();
                while start.elapsed().as_secs_f64() < 0.1 {
                    match GLOBAL_SOLVER.lock().unwrap().do_some_work() {
                        WorkResult::Idle => {
                            println!("No more work to do ({steps} steps total)");
                            done = true;
                            return;
                        }
                        WorkResult::StillWorking => {
                            steps += 1;
                            println!("Did some work");
                        }
                        WorkResult::ProducedOutput(proof) => {
                            println!("Completed {proof}");
                            // println!("Completed proof");
                        }
                    }
                }
                println!("spent {:?} working", start.elapsed());
            });
        }
    });
    // actix_web::rt::spawn(async {
    //     loop {
    //         actix_web::rt::time::sleep(Duration::from_millis(1000)).await;
    //         with_interface(|_| {});
    //     }
    // });
    quick_and_dirty_web_gui::launch("./static/ic_explorer.html", 4987).await;
}
