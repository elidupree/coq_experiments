use crate::global_state_types::{FeaturedInNode, ProofNode};
use crate::serapi_protocol::{IdenticalHypotheses, NamesId};
use serde::{Deserialize, Serialize};

#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct Tactic {
    tactic: String,
    arguments: Option<String>,
}

impl Tactic {
    pub fn from_human_string(string: String) -> Tactic {
        let mut pieces = string.strip_suffix('.').unwrap_or(&string).splitn(2, ' ');
        let tactic = pieces.next().unwrap().to_owned();
        Tactic {
            tactic,
            arguments: pieces.next().map(ToOwned::to_owned),
        }
    }
    pub fn human_string(&self) -> String {
        if let Some(arguments) = &self.arguments {
            format!("{} {}.", self.tactic, arguments)
        } else {
            format!("{}.", self.tactic)
        }
    }
    pub fn coq_string(&self) -> String {
        if let Some(arguments) = &self.arguments {
            format!("progress {} {}.", self.tactic, arguments)
        } else {
            format!("progress {}.", self.tactic)
        }
    }
    pub fn useless(&self, node: &ProofNode) -> bool {
        let child = if let Some(c) = node.child(self) {
            c
        } else {
            return true;
        };
        self.tactic != "clear"
            && self.tactic != "rename"
            && node.state.goals.useless_change(&child.state.goals)
    }
}

const PRIORITY_GLOBAL_TACTICS: &str = "intro.intros.intuition idtac.simpl in *.split.reflexivity.assumption.constructor.exfalso.instantiate.contradiction.discriminate.trivial.inversion_sigma.symmetry.left.right.classical_left.classical_right.solve_constraints.simplify_eq.subst.cbv.lazy.vm_compute.native_compute.red.hnf.cbn.injection.decide equality.tauto.dtauto.congruence.";

const SLOWER_GLOBAL_TACTICS: &str = "firstorder.easy.auto.eauto.auto with *.eauto with *.";

const HYPOTHESIS_TACTICS: &str = "injection H.destruct H.dependent destruction H.induction H.dependent induction H.inversion_clear H.inversion H.dependent inversion H.decompose sum H.decompose record H.apply H.simple apply H.eapply H.rapply H.lapply H.simpl in H.cbv in H.clear H.revert H.generalize H.generalize dependent H.absurd H.contradiction H.contradict H.case H.discriminate H.symmetry in H.simplify_eq H.rewrite <- H. rewrite -> H.rewrite <- H in *. rewrite -> H in *.dependent rewrite <- H. dependent rewrite -> H.";

pub fn generate_exploratory_tactics(
    featured_node: &ProofNode,
    featured_in_node: &FeaturedInNode,
) -> Vec<Tactic> {
    let mut result = Vec::new();
    let first_goal = if let Some(g) = featured_node.state.goals.goals.first() {
        g
    } else {
        return result;
    };

    let mut push = |tactic| {
        result.push(tactic);
    };

    if let FeaturedInNode::Hypothesis {
        name: featured_name,
        subterm: _,
    } = featured_in_node
    {
        for tactic in hypothesis_tactics(featured_name) {
            push(tactic);
        }
    }

    for tactic in PRIORITY_GLOBAL_TACTICS.split('.') {
        push(Tactic {
            tactic: tactic.to_string(),
            arguments: None,
        });
    }
    for IdenticalHypotheses(names, _, _) in &first_goal.hyp {
        for NamesId::Id(name) in names {
            for tactic in hypothesis_tactics(name) {
                push(tactic);
            }
        }
    }
    for tactic in SLOWER_GLOBAL_TACTICS.split('.') {
        push(Tactic {
            tactic: tactic.to_string(),
            arguments: None,
        });
    }
    result
}

pub fn hypothesis_tactics(name: &str) -> impl Iterator<Item = Tactic> + '_ {
    HYPOTHESIS_TACTICS.split('.').map(move |tactic_h| {
        let tactic = tactic_h.replace(" H", "");
        Tactic {
            tactic,
            arguments: Some(name.to_string()),
        }
    })
}

pub fn all_global_tactics() -> impl Iterator<Item = Tactic> {
    PRIORITY_GLOBAL_TACTICS
        .split('.')
        .chain(SLOWER_GLOBAL_TACTICS.split('.'))
        .map(|tactic| Tactic {
            tactic: tactic.to_owned(),
            arguments: None,
        })
}
