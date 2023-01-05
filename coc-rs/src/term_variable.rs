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
    context: ContextVariableId,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Sort {
    Prop,
    Type,
}

pub enum TermValue {
    Variable(TermVariableId),
    Sort(Sort),
    Recursive(RecursiveTermKind, [TermVariableId; 2]),
}

pub struct TermTypeInfo {
    ty: TermVariableId,
    context: ContextVariableId,
}

pub struct ContextVariable {
    value: ContextValue,
}

pub enum ContextValue {
    Variable(ContextVariableId),
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
    pub fn locally_valid(&self, id: TermVariableId) -> bool {
        let variable = self.get_term(id);
        match &term.contents {
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
                context,
            }) => {
                let Some(TermTypeAndValue { type_id: _, value: ty, context: _ }) = self.get_type_and_value(*type_id) else {
                    return value == TermValue::Sort(Sort::Type);
                };

                match value {
                    TermValue::Variable(variable_id) => {
                        let Some(TermTypeAndValue { ty: _, value: expected_type, context: _ }) = self.get_type_and_value(*variable_id) else {
                            return false;
                        };
                        ty == expected_type && self.is_in_context(variable_id, context)
                    }
                    TermValue::Sort(sort) => match sort {
                        Sort::Prop => ty == TermValue::Sort(Sort::Type),
                        Sort::Type => false,
                    },
                    TermValue::Recursive(kind, children) => {
                        let child_types = children
                            .each_ref()
                            .map(|child| self.get_type_and_value(*child));
                        // argtype can be Type, but that still _exists_, it's just its _type_ that doesn't
                        let [Some(lhs), Some(rhs)] = child_types else { return false; };
                        if !self.is_same_context(context, lhs.context) {
                            return false;
                        }

                        use RecursiveTermKind::*;
                        match kind {
                            Lambda | ForAll => {
                                if !self.is_same_context(context, rhs.context) {
                                    return false;
                                }
                            }
                            Apply => {
                                if !self.is_same_context(context, rhs.context) {
                                    return false;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
