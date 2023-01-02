use crate::term::{RecursiveTermKind, Term};

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct IncompleteTermId(usize);

// pub struct CompleteTerm {
//     body: Term,
//     ty: Option<Term>,
//     context_commitments: Vec<IncompleteTermId>,
// }

pub struct IncompleteTerm {
    parents: Vec<IncompleteTermId>,
    body_commitments: Option<IncompleteTermBody>,
    type_commitments: Option<IncompleteTermId>,
    type_judgment: Option<IncompleteTermId>,
    context_commitments: Vec<IncompleteTermId>,
    completion: Option<Term>,
}

pub struct IncompleteTermBody {
    kind: RecursiveTermKind,
    children: [IncompleteTermId; 2],
}

pub struct TermBuildingContext {
    terms: Vec<IncompleteTerm>,
}

impl TermBuildingContext {
    pub fn get(&self, id: IncompleteTermId) -> &IncompleteTerm {
        self.terms.get(id.0).unwrap()
    }
    pub fn get_mut(&mut self, id: IncompleteTermId) -> &mut IncompleteTerm {
        self.terms.get_mut(id.0).unwrap()
    }
    pub fn try_complete(&mut self, id: IncompleteTermId) {
        let left_term = self.get(id);
        let Some(body) = &term.body_commitments else { return; };
        let left = self.get(body.children[0]);
        let right = self.get(body.children[1]);
        let Some(left_type) = left.type_commitments else { return; };
        let Some(right_type) = right.type_commitments else { return; };
        let Some(left_type) = &self.get(left_type).completion else { return; };
        let Some(right_type) = &self.get(right_type).completion else { return; };
        if naive_one_step_type_check(term, left, right) || check_judgment(term, left, right) {
            let Some(left_term) = left.completion.clone() else { return; };
            let Some(right_term) = right.completion.clone() else { return; };
            self.get_mut(id).completion = Some(Term::recursive(body.kind, [left_term, right_term]));
        }
    }
    fn check_judgment(&self, term: &IncompleteTerm) -> bool {
        let Some(type_judgment) = &term.type_judgment else { return false; };
        let type_judgment = self.get(*type_judgment);
        let type_judgment_type = type_judgment.type_commitments else { return false; };
        let Some(type_judgment) = &self.get(type_judgment).completion else { return; };
        let Some(type_judgment_type) = &self.get(type_judgment_type).completion else { return; };
        // type_judgment_type
        //     == "forall judgment of left type, judgment of right type, judgment of term type"
    }
}
