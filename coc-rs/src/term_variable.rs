use crate::term::RecursiveTermKind;
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct TermVariableId(usize);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ContextVariableId(usize);

pub struct TermVariable {
    name: String,
    contents: TermContents,

    parent: Option<TermVariableId>,
    back_references: Vec<TermVariableId>,
}

pub enum TermContents {
    Nothing,
    Reference(TermVariableId),
    Term(TermTypeAndValue),
}

pub struct TermTypeAndValue {
    value: TermValue,
    type_id: TermVariableId,
    context_id: ContextVariableId,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Sort {
    Prop,
    Type,
}

#[derive(Clone, Copy, Debug)]
pub enum TermValue {
    Variable(TermVariableId),
    Sort(Sort),
    Recursive(RecursiveTermKind, [TermVariableId; 2]),
}

pub enum ContextVariable {
    Reference(ContextVariableId),
    Value(ContextValue),
}

pub enum ContextValue {
    Nil,
    Cons(TermVariableId, ContextVariableId),
}

pub struct Environment {
    terms: HashMap<TermVariableId, TermVariable>,
    contexts: HashMap<ContextVariableId, ContextVariable>,
}

impl Environment {
    pub fn get_term(&self, id: TermVariableId) -> &TermVariable {
        self.terms.get(&id).unwrap()
    }
    pub fn get_type_and_value(&self, id: TermVariableId) -> Option<&TermTypeAndValue> {
        let mut id = id;
        loop {
            match &self.get_term(id).contents {
                TermContents::Nothing => return None,
                TermContents::Reference(id2) => id = *id2,
                TermContents::Term(t) => return Some(t),
            }
        }
    }
    pub fn get_context(&self, id: ContextVariableId) -> &ContextVariable {
        self.contexts.get(&id).unwrap()
    }
    pub fn get_context_value(&self, id: ContextVariableId) -> &ContextValue {
        let mut id = id;
        loop {
            match self.get_context(id) {
                ContextVariable::Reference(id2) => id = *id2,
                ContextVariable::Value(c) => return c,
            }
        }
    }
    pub fn is_in_context(
        &self,
        variable_id: TermVariableId,
        context_id: ContextVariableId,
    ) -> bool {
        let mut context_id = context_id;
        loop {
            match self.get_context_value(context_id) {
                ContextValue::Nil => return false,
                ContextValue::Cons(head_id, tail_id) => {
                    // deliberately use variable-identity
                    if *head_id == variable_id {
                        return true;
                    }
                    context_id = *tail_id;
                }
            }
        }
    }
    pub fn is_same_context(&self, a: ContextVariableId, b: ContextVariableId) -> bool {
        let (mut a, mut b) = (a, b);
        loop {
            match (self.get_context_value(a), self.get_context_value(b)) {
                (ContextValue::Nil, ContextValue::Nil) => return true,
                (ContextValue::Cons(ah, at), ContextValue::Cons(bh, bt))
                    // deliberately use variable-identity
                    if ah == bh => {
                    a = *at;
                    b = *bt;
                }
                _ => return false,
            }
        }
    }
    pub fn is_same_term(&self, a: TermVariableId, b: TermVariableId) -> bool {}
    pub fn is_term_with_substitution(
        &self,
        a: TermVariableId,
        b: TermVariableId,
        replaced: TermVariableId,
        replacement: TermVariableId,
    ) -> bool {
    }
    pub fn locally_valid(&self, id: TermVariableId) -> bool {
        let variable = self.get_term(id);
        match &variable.contents {
            TermContents::Nothing => {
                // `Nothing` is not intrinsically invalid – it is only invalid to use it as a value
                true
            }
            TermContents::Reference(_other_id) => {
                // we don't need to duplicate the work of checking whether other_id is valid
                // or the work of checking whether our parent is valid based on what our value is
                true
            }
            TermContents::Term(TermTypeAndValue {
                type_id,
                value,
                context_id,
            }) => {
                let Some(TermTypeAndValue { type_id: _, value: ty, context_id: _ }) = self.get_type_and_value(*type_id) else {
                    return matches!(value, TermValue::Sort(Sort::Type));
                };

                match value {
                    TermValue::Variable(variable_id) => {
                        self.is_same_term(*type_id, *variable_id)
                            && self.is_in_context(*variable_id, *context_id)
                    }
                    TermValue::Sort(sort) => match sort {
                        // note: this allows Prop : Type in any context, not just the empty context
                        Sort::Prop => matches!(ty, TermValue::Sort(Sort::Type)),
                        Sort::Type => false,
                    },
                    TermValue::Recursive(kind, child_ids) => {
                        let child_info = child_ids
                            .each_ref()
                            .map(|child| self.get_type_and_value(*child));
                        let [Some(lhs), Some(rhs)] = child_info else { return false; };
                        let Some(TermTypeAndValue { type_id: _, value: lhs_type, context_id: _ }) = self.get_type_and_value(lhs.type_id) else {
                            return false;
                        };
                        let Some(TermTypeAndValue { type_id: _, value: rhs_type, context_id: _ }) = self.get_type_and_value(rhs.type_id) else {
                            return false;
                        };
                        if !self.is_same_context(*context_id, lhs.context_id) {
                            return false;
                        }

                        use RecursiveTermKind::*;
                        match kind {
                            Lambda | ForAll => {
                                if !matches!(lhs_type, TermValue::Sort(_)) {
                                    return false;
                                }
                                let body_context = self.get_context_value(rhs.context_id);
                                let ContextValue::Cons(body_context_head, body_context_tail) = body_context else { return false; };
                                if !self.is_same_term(*body_context_head, child_ids[0]) {
                                    return false;
                                }
                                if !self.is_same_context(*context_id, *body_context_tail) {
                                    return false;
                                }
                                match kind {
                                    Lambda => {
                                        let TermValue::Recursive(ForAll, [type_lhs_id, type_rhs_id]) = ty else { return false; };
                                        self.is_same_term(*type_lhs_id, child_ids[0])
                                            && self.is_same_term(*type_rhs_id, rhs.type_id)
                                    }
                                    ForAll => {
                                        matches!(ty, TermValue::Sort(_))
                                            && self.is_same_term(*type_id, rhs.type_id)
                                    }
                                    Apply => unreachable!(),
                                }
                            }
                            Apply => {
                                if !self.is_same_context(*context_id, rhs.context_id) {
                                    return false;
                                }
                                let TermValue::Recursive(ForAll, [type_lhs_id, type_rhs_id]) = lhs_type else { return false; };
                                self.is_same_term(*type_lhs_id, rhs.type_id)
                                    && self.is_term_with_substitution(
                                        *type_id,
                                        *type_rhs_id,
                                        *type_lhs_id,
                                        child_ids[0],
                                    )
                            }
                        }
                    }
                }
            }
        }
    }
}
