use crate::interface::Element;
use crate::serapi_protocol::{ConstrExpr, IdenticalHypotheses, NamesId, ReifiedGoal, SerGoals};
use difference::{Changeset, Difference};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
use typed_html::{html, text};

pub type Goals<A> = SerGoals<ReifiedGoal<A>>;

impl<A> Goals<A> {
    pub fn map_values<B>(self, mut convert: impl FnMut(A) -> B) -> Goals<B> {
        SerGoals {
            goals: self
                .goals
                .into_iter()
                .map(|g| g.map_values(|a| convert(a)))
                .collect(),
            stack: self.stack,
            shelf: self.shelf,
            given_up: self.given_up,
            bullet: self.bullet,
        }
    }
}
impl<A> ReifiedGoal<A> {
    pub fn map_values<B>(self, mut convert: impl FnMut(A) -> B) -> ReifiedGoal<B> {
        ReifiedGoal {
            info: self.info,
            ty: convert(self.ty),
            hyp: self
                .hyp
                .into_iter()
                .map(|h| h.map_values(|a| convert(a)))
                .collect(),
        }
    }
}

impl<A> IdenticalHypotheses<A> {
    pub fn map_values<B>(self, mut convert: impl FnMut(A) -> B) -> IdenticalHypotheses<B> {
        let IdenticalHypotheses(name, def, ty) = self;
        IdenticalHypotheses(name, def.map(|a| convert(a)), convert(ty))
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct CoqValueInfo {
    pub constr_expr: ConstrExpr,
    pub string: String,
}

impl fmt::Display for CoqValueInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.string, f)
    }
}

impl fmt::Display for IdenticalHypotheses<CoqValueInfo> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let IdenticalHypotheses(names, def, ty) = self;
        let names: Vec<_> = names
            .iter()
            .map(|NamesId::Id(name)| name.as_str())
            .collect();
        let names = names.join(", ");
        if let Some(def) = def.as_ref() {
            write!(f, "{} := {} : {}", names, def, ty)
        } else {
            write!(f, "{} : {}", names, ty)
        }
    }
}

impl ReifiedGoal<CoqValueInfo> {
    pub fn hypothesis_strings(&self) -> Vec<String> {
        self.hyp.iter().map(ToString::to_string).collect()
    }

    pub fn html(&self) -> Element {
        let hypotheses_string = self.hypothesis_strings().join("\n");
        let conclusion_string = &self.ty.string;
        html! {
            <div class="goal">
                <pre>{text!("{}", hypotheses_string)}</pre>
                <hr/>
                <pre>{text!("{}", conclusion_string)}</pre>
            </div>
        }
    }

    /// approximate detection of changes that are useless.
    ///
    /// We suppose that a change is potentially useful if it changes the conclusion, or if it adds a hypothesis with a type that didn't appear among the parent's hypotheses. Thus, clearing and renaming are "useless"
    pub fn useless_change(&self, child: &ReifiedGoal<CoqValueInfo>) -> bool {
        child.ty == self.ty
            && child.hyp.iter().all(|IdenticalHypotheses(_, cd, ct)| {
                self.hyp
                    .iter()
                    .any(|IdenticalHypotheses(_, pd, pt)| pd == cd && pt == ct)
            })
    }
}

impl Goals<CoqValueInfo> {
    pub fn html(&self) -> Element {
        html! {
            <div class="goals">
                {self.goals.iter().map(|g| g.html())}
            </div>
        }
    }

    /// approximate detection of changes that are useless.
    ///
    /// Our logic for multiple goals is that a change is useless if, for every goal in the parent, there exists a goal in the child that is a useless change from it. Thus, you couldn't solve the child without solving every goal from the parent just as easily.
    pub fn useless_change(&self, child: &Goals<CoqValueInfo>) -> bool {
        self.goals
            .iter()
            .all(|parent| child.goals.iter().any(|child| parent.useless_change(child)))
    }

    pub fn diff_html(&self, child: &Goals<CoqValueInfo>) -> Element {
        let first_goal = self.goals.first().unwrap();
        let relevant_goals = &child.goals[..child.goals.len() + 1 - self.goals.len()];
        let mut elements: Vec<Element> = Vec::new();
        if relevant_goals.is_empty() {
            elements
                .push(html! { <ins><pre class="diff">{text!("Current goal solved!")}</pre></ins> })
        }

        let parent_hypotheses_string = first_goal.hypothesis_strings().join("\n");
        let parent_conclusion_string = &first_goal.ty.string;

        for goal in relevant_goals {
            let child_hypotheses_string = goal.hypothesis_strings().join("\n");
            let child_conclusion_string = &goal.ty.string;

            let hypotheses_diff =
                Changeset::new(&parent_hypotheses_string, &child_hypotheses_string, "\n");
            for item in hypotheses_diff.diffs {
                match item {
                    Difference::Add(added) => {
                        elements.push(html! {
                            <ins class="line"><pre>{text!("{}", added)}</pre></ins>
                        });
                    }
                    Difference::Rem(removed) => {
                        elements.push(html! {
                            <del class="line"><pre>{text!("{}", removed)}</pre></del>
                        });
                    }
                    _ => {}
                }
            }
            elements.push(html! {
                <hr/>
            });
            if parent_conclusion_string != child_conclusion_string {
                let conclusion_diff =
                    Changeset::new(&parent_conclusion_string, child_conclusion_string, "");
                let mut old: Vec<Element> = Vec::new();
                let mut new: Vec<Element> = Vec::new();
                let mut any_added = false;
                let mut any_removed = false;
                for item in conclusion_diff.diffs {
                    match item {
                        Difference::Add(added) => {
                            any_added = true;
                            new.push(html! {
                                <ins><pre>{text!("{}", added)}</pre></ins>
                            });
                        }
                        Difference::Rem(removed) => {
                            any_removed = true;
                            old.push(html! {
                                <del><pre>{text!("{}", removed)}</pre></del>
                            });
                        }
                        Difference::Same(same) => {
                            new.push(html! {
                                <pre>{text!("{}", same)}</pre>
                            });
                            old.push(html! {
                                <pre>{text!("{}", same)}</pre>
                            });
                        }
                    }
                }
                if any_removed {
                    elements.push(html! {
                        <div>{old}</div>
                    });
                }
                if any_added {
                    elements.push(html! {
                        <div>{new}</div>
                    });
                }
            }
            elements.push(html! {
                <hr/>
            });
        }
        if !relevant_goals.is_empty() {
            elements.pop();
        }

        html! {
            <div class="goals_diff">
                {elements}
            </div>
        }
    }

    pub fn only_difference_in_hypothesis_html(
        &self,
        child: &Goals<CoqValueInfo>,
        hypothesis_name: &str,
    ) -> Option<Element> {
        if child.goals.is_empty() || child.goals.len() != self.goals.len() {
            return None;
        }
        if child.goals[self.goals.len() - 1] != self.goals[self.goals.len() - 1] {
            return None;
        }
        let parent = self.goals.last().unwrap();
        let child = child.goals.last().unwrap();
        let parent_hypotheses: HashMap<&str, _> = parent
            .hyp
            .iter()
            .flat_map(move |IdenticalHypotheses(names, def, ty)| {
                names
                    .iter()
                    .map(move |NamesId::Id(name)| (name.as_str(), (def, ty)))
            })
            .collect();
        let mut result: Option<Element> = None;
        for h in &child.hyp {
            let IdenticalHypotheses(names, def, ty) = h;
            for NamesId::Id(name) in names {
                if name != hypothesis_name
                    && parent_hypotheses.get(name.as_str()) != Some(&(def, ty))
                {
                    return None;
                }
                if name == hypothesis_name {
                    result = Some(html! { <pre>{text!("{}", h)}</pre>});
                }
            }
        }
        result
    }
}
