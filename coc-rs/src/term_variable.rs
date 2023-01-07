use crate::term::RecursiveTermKind;
use std::collections::HashMap;
use std::iter;
use uuid::Uuid;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct TermVariableId(Uuid);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ContextVariableId(Uuid);

pub struct TermVariable {
    pub name: String,
    pub contents: TermContents,

    pub parent: Option<TermVariableId>,
    pub back_references: Vec<TermVariableId>,
}

pub enum TermContents {
    Nothing,
    Reference(TermVariableId),
    Term(TermTypeAndValue),
}

pub struct TermTypeAndValue {
    pub value: TermValue,
    pub type_id: TermVariableId,
    pub context_id: ContextVariableId,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Sort {
    Prop,
    Type,
}

#[derive(Clone, Copy, Debug)]
pub enum TermValue {
    VariableUsage(TermVariableId),
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
    fn get_term_mut(&mut self, id: TermVariableId) -> &mut TermVariable {
        self.terms.get_mut(&id).unwrap()
    }
    pub fn unrolled_variable(
        &self,
        id: TermVariableId,
    ) -> (TermVariableId, Option<&TermTypeAndValue>) {
        let mut walking_id = id;
        for _ in 0..10000 {
            match &self.get_term(walking_id).contents {
                TermContents::Nothing => return (walking_id, None),
                TermContents::Reference(id2) => walking_id = *id2,
                TermContents::Term(t) => return (walking_id, Some(t)),
            }
        }
        println!(
            "Warning: Excess depth, probably recursive variable reference, in {:?}",
            id
        );
        return (id, None);
    }
    pub fn unrolled_variable_with_substitution(
        &self,
        id: TermVariableId,
        replaced: TermVariableId,
        replacement: TermVariableId,
    ) -> (TermVariableId, Option<&TermTypeAndValue>) {
        let mut walking_id = id;
        for _ in 0..10000 {
            if walking_id == replaced {
                walking_id = replacement;
            }
            match &self.get_term(walking_id).contents {
                TermContents::Nothing => return (walking_id, None),
                TermContents::Reference(id2) => walking_id = *id2,
                TermContents::Term(t) => return (walking_id, Some(t)),
            }
        }
        println!(
            "Warning: Excess depth, probably recursive variable reference, in {:?}[{:?} := {:?}]",
            id, replaced, replacement
        );
        return (id, None);
    }
    pub fn get_type_and_value(&self, id: TermVariableId) -> Option<&TermTypeAndValue> {
        self.unrolled_variable(id).1
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
    pub fn is_same_term(&self, a: TermVariableId, b: TermVariableId) -> bool {
        let (a, av) = self.unrolled_variable(a);
        let (b, bv) = self.unrolled_variable(b);
        if a == b {
            return true;
        }
        let Some(TermTypeAndValue { type_id: _, value: a, context_id: _ }) = av else { return false; };
        let Some(TermTypeAndValue { type_id: _, value: b, context_id: _ }) = bv else { return false; };
        match (a, b) {
            (TermValue::VariableUsage(a), TermValue::VariableUsage(b)) => a == b,
            (TermValue::Sort(a), TermValue::Sort(b)) => a == b,
            (TermValue::Recursive(ak, ac), TermValue::Recursive(bk, bc)) => {
                ak == bk && iter::zip(ac, bc).all(|(a, b)| self.is_same_term(*a, *b))
            }
            _ => false,
        }
    }
    pub fn is_term_with_substitution(
        &self,
        a: TermVariableId,
        b: TermVariableId,
        replaced: TermVariableId,
        replacement: TermVariableId,
    ) -> bool {
        let (a, av) = self.unrolled_variable_with_substitution(a, replaced, replacement);
        let (b, bv) = self.unrolled_variable_with_substitution(b, replaced, replacement);
        if a == b {
            return true;
        }
        let Some(TermTypeAndValue { type_id: _, value: a, context_id: _ }) = av else { return false; };
        let Some(TermTypeAndValue { type_id: _, value: b, context_id: _ }) = bv else { return false; };
        match (a, b) {
            (TermValue::VariableUsage(a), TermValue::VariableUsage(b)) => a == b,
            (TermValue::Sort(a), TermValue::Sort(b)) => a == b,
            (TermValue::Recursive(ak, ac), TermValue::Recursive(bk, bc)) => {
                ak == bk && iter::zip(ac, bc).all(|(a, b)| self.is_same_term(*a, *b))
            }
            _ => false,
        }
    }
    pub fn locally_valid(&self, id: TermVariableId) -> bool {
        let variable = self.get_term(id);
        let TermTypeAndValue {
            type_id,
            value,
            context_id,
        } = match &variable.contents {
            TermContents::Nothing => {
                // `Nothing` is not intrinsically invalid – it is only invalid to use it as a value
                return true;
            }
            TermContents::Reference(_other_id) => {
                // we don't need to duplicate the work of checking whether other_id is valid
                // or the work of checking whether our parent is valid based on what our value is
                return true;
            }
            TermContents::Term(t) => t,
        };

        let Some(TermTypeAndValue { type_id: _, value: ty, context_id: _ }) = self.get_type_and_value(*type_id) else {
            return matches!(value, TermValue::Sort(Sort::Type));
        };

        match value {
            TermValue::VariableUsage(variable_id) => {
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

    pub fn new() -> Self {
        todo!()
    }
    pub fn clear(&mut self, id: TermVariableId) {
        let contents =
            std::mem::replace(&mut self.get_term_mut(id).contents, TermContents::Nothing);
        let TermTypeAndValue {
            type_id,
            value,
            context_id,
        } = match contents {
            TermContents::Nothing => {
                // Already done
                return;
            }
            TermContents::Reference(other_id) => {
                self.get_term_mut(other_id)
                    .back_references
                    .retain(|i| *i != id);
                return;
            }
            TermContents::Term(t) => t,
        };
        //self.get_term_mut(type_id).parent.retain(|i| *i != id);

        match value {
            TermValue::VariableUsage(other_id) => {
                self.get_term_mut(other_id)
                    .back_references
                    .retain(|i| *i != id);
                return;
            }
            TermValue::Sort(_) => {}
            TermValue::Recursive(_, _) => {}
        }
    }
    pub fn make_reference(&mut self, id: TermVariableId, target: TermVariableId) {
        self.clear(id);
    }
    pub fn make_variable_usage(&mut self, id: TermVariableId, target: TermVariableId) {
        self.clear(id);
    }
    pub fn make_new_recursive_term(&mut self, id: TermVariableId, kind: RecursiveTermKind) {
        self.clear(id);
    }
}
