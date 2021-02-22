use crate::global_state_types::{Featured, FeaturedInNode, ProofNode, SharedState};
use crate::global_state_types::{Mode, TacticResult};
use crate::goals_analysis::CoqValueInfo;
use crate::serapi_protocol::{IdenticalHypotheses, NamesId};
use crate::tactics;
use crate::tactics::Tactic;
use guard::guard;
use std::time::Duration;
use typed_html::elements::FlowContent;
use typed_html::{html, text};

pub type Element = Box<dyn FlowContent<String>>;

impl SharedState {
    fn tactic_menu_html(&self, tactics: impl IntoIterator<Item = Tactic>) -> Element {
        guard!(let Some(Mode::ProofMode(_proof_root, featured)) = &self.known_mode else {unreachable!()});
        let (featured_node, _) = self.featured_node().unwrap();
        let entries = tactics.into_iter().map(|tactic| {
            guard!(let Some(TacticResult::Success { duration, result_node })
                = featured_node.attempted_tactics.get(&tactic) else {panic!("tactic_menu_html doesn't support entries for failing tactics yet")});
            let name = tactic.human_string();
            let onclick = featured.extended(tactic).input_string();

            let duration: Option<Element> = if duration > &Duration::from_millis(50) {
                Some(html! {
                    <div class="duration">
                        {text!("Took {}ms", duration.as_millis())}
                    </div>
                })
            } else {
                None
            };
            html! {
                <div class="tactic_entry" data-onclick={onclick}>
                    <pre class="tactic">{text!("{}", name)}</pre>
                    <div class="popup_result">
                        {duration}
                        {featured_node.state.goals.diff_html(&result_node.state.goals)}
                    </div>
                </div>
            }
        });
        html! {
            <div class="tactic_menu">{entries}</div>
        }
    }

    fn attempted_tactics_html(&self) -> Vec<Element> {
        let (featured_node, _) = self.featured_node().unwrap();
        let first_goal = match featured_node.state.goals.goals.first() {
            Some(goal) => goal,
            None => {
                return vec![text!(
                "All goals solved! (Except maybe shelved goals, I haven't implemented that yet)."
            )]
            }
        };

        let mut solvers: Vec<_> =
            tactics::generate_exploratory_tactics(featured_node, &FeaturedInNode::Nothing)
                .into_iter()
                .filter(|tactic| !tactic.useless(featured_node))
                .filter(|tactic| {
                    featured_node
                        .child(tactic)
                        .expect("unsuccessful tactics should've been useless")
                        .state
                        .goals
                        .goals
                        .len()
                        < featured_node.state.goals.goals.len()
                })
                .collect();
        let mut results: Vec<Element> = Vec::new();
        let solved = !solvers.is_empty();
        if solved {
            fn proof_length_fn(featured_node: &ProofNode, tactic: &Tactic) -> usize {
                featured_node
                    .child(tactic)
                    .unwrap()
                    .state
                    .proof_string
                    .as_ref()
                    .map_or(1 << 30, String::len)
            }
            solvers.sort_by_key(|t| (proof_length_fn)(featured_node, t));
            let best_size = (proof_length_fn)(featured_node, &solvers[0]);
            let (best_solvers, worse_solvers): (Vec<_>, Vec<_>) = solvers
                .into_iter()
                .partition(|tactic| (proof_length_fn)(featured_node, tactic) == best_size);
            let best_solvers = self.tactic_menu_html(best_solvers);
            let worse_solvers: Vec<Element> = if worse_solvers.is_empty() {
                Vec::new()
            } else {
                vec![
                    html! {
                        <h3>
                            {text!("These also solve it, but they make larger proofs:")}
                        </h3>
                    },
                    self.tactic_menu_html(worse_solvers),
                ]
            };
            results.push(html! {
                <div class="solvers">
                    <h2>
                        {text!("This goal is immediately solved by:")}
                    </h2>
                    {best_solvers}
                    {worse_solvers}
                </div>
            })
        }

        let global_tactics = self.tactic_menu_html(
            tactics::all_global_tactics()
                .filter(|tactic| !tactic.useless(featured_node))
                .filter(|tactic| {
                    featured_node
                        .child(tactic)
                        .expect("unsuccessful tactics should've been useless")
                        .state
                        .goals
                        .goals
                        .len()
                        >= featured_node.state.goals.goals.len()
                }),
        );
        let hyp_note = if first_goal.hyp.is_empty() {
            None
        } else {
            Some(html! {
                <div class="click_hypotheses_note">
                    {text!("(Or click one of the hypothesis names to the left, to see tactics related to that hypothesis.)")}
                </div>
            })
        };
        if solved {
            results.push(html! {
                <div class="global_tactics">
                    <h2 class="deemphasize">
                        {text!("(These don't solve it:)")}
                    </h2>
                    {global_tactics}
                    {hyp_note}
                </div>
            });
        } else {
            results.push(html! {
                <div class="global_tactics">
                    <h2>
                        {text!("Try one of these tactics:")}
                    </h2>
                    {global_tactics}
                    {hyp_note}
                </div>
            });
        }

        results
    }
    fn hypothesis_html(
        &self,
        hypothesis: &IdenticalHypotheses<CoqValueInfo>,
        featured: &Featured,
    ) -> Element {
        let IdenticalHypotheses(names, def, ty) = &hypothesis;
        let (featured_node, featured_in_node) = self.featured_node().unwrap();
        let mut elements: Vec<Element> = Vec::new();
        for NamesId::Id(name) in names {
            let mut featured_toggling_this = featured.clone();
            {
                let featuring_this = FeaturedInNode::Hypothesis {
                    name: name.clone(),
                    subterm: None,
                };
                let f = featured_toggling_this.featured_in_current_mut();
                if *f == featuring_this {
                    *f = FeaturedInNode::Nothing;
                } else {
                    *f = FeaturedInNode::Hypothesis {
                        name: name.clone(),
                        subterm: None,
                    };
                }
            }
            let onclick = featured_toggling_this.input_string();

            let mut class = "hypothesis_name_wrapper not_featured";
            let mut dropdown: Option<Element> = None;
            if let FeaturedInNode::Hypothesis {
                name: featured_name,
                subterm,
            } = featured_in_node
            {
                if featured_name == name {
                    class = "hypothesis_name_wrapper featured";

                    dropdown = Some(
                        self.tactic_menu_html(
                            tactics::hypothesis_tactics(name)
                                .filter(|tactic| !tactic.useless(featured_node)),
                        ),
                    );
                }
            }

            elements.push(html! {
                <div class={class} data-onclick={onclick}>
                    <pre class="hypothesis_name">{text!("{}", name)}</pre>
                    {dropdown}
                </div>
            });
            elements.push(html! { <pre>{text!(", ")}</pre> });
        }
        elements.pop();

        if let Some(def) = def {
            elements.push(html! { <pre>{text!(" := {}", def.string)}</pre> });
        }

        elements.push(html! { <pre>{text!(" : {}", ty.string)}</pre> });

        html! {
            <div class="hypothesis">
                {elements}
            </div>
        }
    }
    fn conclusion_html(&self, _featured: &Featured) -> Element {
        let (featured_node, _featured_in_node) = self.featured_node().unwrap();
        html! {
            <div class="conclusion">
                <pre>{text!("{}", featured_node.state.goals.goals.first().unwrap().ty.string)}</pre>
            </div>
        }
    }

    pub fn whole_interface_html(&self) -> Element {
        let (proof_root, featured): (&ProofNode, &Featured) = match &self.known_mode {
            None => return text!("Processing..."),
            Some(Mode::NotProofMode) => return text!("Not in proof mode"),
            Some(Mode::ProofMode(p, f)) => (p, f),
        };

        let featured_node = proof_root.descendant(featured.tactics_path()).unwrap();
        let attempted_tactics = self.attempted_tactics_html();
        let mut prior_tactics: Vec<Element> = Vec::new();
        for (index, (tactic, _)) in featured.tactics.iter().enumerate() {
            let featured_after_this_tactic = Featured {
                num_tactics_run: index + 1,
                ..featured.clone()
            };
            let node = proof_root
                .descendant(featured_after_this_tactic.tactics_path())
                .unwrap();
            let onclick = featured_after_this_tactic.input_string();
            let class = if index + 1 < featured.num_tactics_run {
                "prior_tactic past not_present"
            } else if index + 1 == featured.num_tactics_run {
                "prior_tactic present"
            } else {
                "prior_tactic future not_present"
            };
            prior_tactics.push(html! {
                <div class={class} data-onclick={onclick}>
                    <div class="tactic">
                        <pre>{text!("{}", tactic.human_string())}</pre>
                    </div>
                    {node.state.goals.html()}
                </div>
            });
        }
        if !prior_tactics.is_empty() {
            prior_tactics = vec![html! {
                <div class="prior_tactics_row">
                    <h2>
                        {text!("And you've already done this stuff:")}
                    </h2>
                    <div class="prior_tactics">
                        {prior_tactics}
                    </div>
                </div>
            }]
        }

        let current_goal: Option<Element> =
            featured_node.state.goals.goals.first().map(|first_goal| {
                let conclusion = self.conclusion_html(featured);
                let result: Element = if first_goal.hyp.is_empty() {
                    html! {
                        <div class="current_goal">
                            <h2>
                                {text!("Now you want to prove this:")}
                            </h2>
                            {conclusion}
                        </div>
                    }
                } else {
                    let hypotheses = first_goal
                        .hyp
                        .iter()
                        .map(|h| self.hypothesis_html(h, featured));
                    html! {
                        <div class="current_goal">
                            <h2>
                                {text!("Now you know this stuff:")}
                            </h2>
                            {hypotheses}
                            <h2>
                                {text!("And you want to prove this:")}
                            </h2>
                            {conclusion}
                        </div>
                    }
                };
                result
            });

        let onclick_root_featured = Featured {
            num_tactics_run: 0,
            ..featured.clone()
        };
        let onclick_root = onclick_root_featured.input_string();
        let proof_root_class = if featured.num_tactics_run > 0 {
            "proof_root past not_present"
        } else {
            "proof_root present"
        };

        let mut featured_deselecting = featured.clone();
        *featured_deselecting.featured_in_current_mut() = FeaturedInNode::Nothing;
        let onclick_default = featured_deselecting.input_string();

        html! {
            <div class="whole_interface" data-onclick={onclick_default}>
                <div class={proof_root_class} data-onclick={onclick_root}>
                    <h2>
                        {text!("So you started with this:")}
                    </h2>
                    {proof_root.state.goals.html()}
                </div>
                {prior_tactics}
                <div class="main_area">
                    {current_goal}
                    {attempted_tactics}
                </div>
            </div>
        }
    }
}
