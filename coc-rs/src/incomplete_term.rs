use crate::term::{RecursiveTermKind, Term};

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
    type_judgment: IncompleteTermId,
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
    pub fn try_complete(&mut self, id: IncompleteTermId) {
        let term = self.get(id);
        let Some (body) =&term.body_commitments else {return};
        let left = self.get(body.children[0]);
        let right = self.get(body.children[1]);
    }
}
