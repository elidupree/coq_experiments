use crate::interface::{FeaturedInState, ProofState};
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
    pub fn useless(&self, state: &ProofState) -> bool {
        let child = if let Some(c) = state.child(self) {
            c
        } else {
            return true;
        };
        self.tactic != "clear"
            && self.tactic != "rename"
            && state.goals.useless_change(&child.goals)
    }
}

const PRIORITY_GLOBAL_TACTICS: &str = "intro.intros.intuition idtac.simpl in *.split.reflexivity.assumption.constructor.exfalso.instantiate.contradiction.discriminate.trivial.inversion_sigma.symmetry.left.right.classical_left.classical_right.solve_constraints.simplify_eq.subst.cbv.lazy.vm_compute.native_compute.red.hnf.cbn.injection.decide equality.tauto.dtauto.congruence.";

const SLOWER_GLOBAL_TACTICS: &str = "firstorder.easy.auto.eauto.auto with *.eauto with *.";

const HYPOTHESIS_TACTICS: &str = "simpl in H.cbv in H.injection H.apply H.simple apply H.eapply H.rapply H.lapply H.clear H.revert H.decompose sum H.decompose record H.generalize H.generalize dependent H.absurd H.contradiction H.contradict H.destruct H.case H.induction H.dependent destruction H.dependent induction H.inversion H.discriminate H.inversion_clear H.dependent inversion H.symmetry in H.simplify_eq H.rewrite <- H. rewrite -> H.rewrite <- H in *. rewrite -> H in *.dependent rewrite <- H. dependent rewrite -> H.";

pub fn generate_exploratory_tactics(
    featured_state: &ProofState,
    featured_in_state: &FeaturedInState,
) -> Vec<Tactic> {
    let mut result = Vec::new();
    let first_goal = if let Some(g) = featured_state.goals.goals.first() {
        g
    } else {
        return result;
    };

    let mut push = |tactic| {
        if featured_state.attempted_tactics.get(&tactic).is_none() {
            result.push(tactic);
        }
    };

    if let FeaturedInState::Hypothesis {
        name: featured_name,
        subterm: _,
    } = featured_in_state
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
