use crate::term::RecursiveTermKind;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::iter;
use uuid::Uuid;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Debug)]
pub struct TermVariableId(pub Uuid);

#[derive(Default, Serialize, Deserialize, Debug)]
pub struct TermVariable {
    pub name: String,
    pub contents: TermContents,

    pub parent: Option<TermVariableId>,
    pub back_references: Vec<TermVariableId>,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
pub enum TermContents {
    Nothing,
    Reference(TermVariableId),
    Term(TermTypeAndValue),
}

impl Default for TermContents {
    fn default() -> Self {
        TermContents::Nothing
    }
}

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct TermTypeAndValue {
    pub value: TermValue,
    pub type_id: TermVariableId,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Debug)]
pub enum Sort {
    Prop,
    Type,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
pub enum TermValue {
    VariableUsage(TermVariableId),
    Sort(Sort),
    Recursive(RecursiveTermKind, [TermVariableId; 2]),
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Environment {
    terms: HashMap<TermVariableId, TermVariable>,
}

pub enum ElementaryDisproofsOfElementaryJudgments {
    NotAnActualTerm,
    Type {
        has_type: bool,
    },
    Prop {
        type_is_not_t: bool,
    },
    Variable {
        type_not_known_to_be_definitionally_equal_to_binding_type: bool,
    },
    ForAll {
        argument_type_type_is_not_sort: bool,
        type_is_not_sort: bool,
        return_type_type_is_not_sort: bool,
        type_not_known_to_be_definitionally_equal_to_return_type_type: bool,
    },
    Lambda {
        argument_type_type_is_not_sort: bool,
        type_is_not_forall: bool,
        argument_type_not_known_to_be_definitionally_equal_to_type_argument_type: bool,
        body_type_not_known_to_be_definitionally_equal_to_type_return_type: bool,
    },
    Apply {
        lhs_type_is_not_forall: bool,
        lhs_argument_type_not_known_to_be_definitionally_equal_to_rhs_type: bool,
        type_not_known_to_be_definitionally_equal_to_substituted_lhs_return_type: bool,
    },
}

impl ElementaryDisproofsOfElementaryJudgments {
    fn is_invalid(&self) -> bool {
        match *self {
            ElementaryDisproofsOfElementaryJudgments::NotAnActualTerm => false,
            ElementaryDisproofsOfElementaryJudgments::Type { has_type } => has_type,
            ElementaryDisproofsOfElementaryJudgments::Prop { type_is_not_t } => type_is_not_t,
            ElementaryDisproofsOfElementaryJudgments::Variable {
                type_not_known_to_be_definitionally_equal_to_binding_type,
            } => type_not_known_to_be_definitionally_equal_to_binding_type,
            ElementaryDisproofsOfElementaryJudgments::ForAll {
                argument_type_type_is_not_sort,
                type_is_not_sort,
                return_type_type_is_not_sort: return_type_is_not_sort,
                type_not_known_to_be_definitionally_equal_to_return_type_type:
                    type_not_known_to_be_definitionally_equal_to_return_type,
            } => {
                argument_type_type_is_not_sort
                    || type_is_not_sort
                    || return_type_is_not_sort
                    || type_not_known_to_be_definitionally_equal_to_return_type
            }
            ElementaryDisproofsOfElementaryJudgments::Lambda {
                argument_type_type_is_not_sort,
                type_is_not_forall: type_not_is_not_forall,
                argument_type_not_known_to_be_definitionally_equal_to_type_argument_type,
                body_type_not_known_to_be_definitionally_equal_to_type_return_type:
                    type_of_body_not_known_to_be_definitionally_equal_to_type_return_type,
            } => {
                argument_type_type_is_not_sort
                    || type_not_is_not_forall
                    || argument_type_not_known_to_be_definitionally_equal_to_type_argument_type
                    || type_of_body_not_known_to_be_definitionally_equal_to_type_return_type
            }
            ElementaryDisproofsOfElementaryJudgments::Apply {
                lhs_type_is_not_forall,
                lhs_argument_type_not_known_to_be_definitionally_equal_to_rhs_type,
                type_not_known_to_be_definitionally_equal_to_substituted_lhs_return_type,
            } => {
                lhs_type_is_not_forall
                    || lhs_argument_type_not_known_to_be_definitionally_equal_to_rhs_type
                    || type_not_known_to_be_definitionally_equal_to_substituted_lhs_return_type
            }
        }
    }
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
    ) -> Option<(TermVariableId, Option<&TermTypeAndValue>)> {
        let mut walking_id = id;
        for _ in 0..10000 {
            match &self.get_term(walking_id).contents {
                TermContents::Nothing => return Some((walking_id, None)),
                TermContents::Reference(id2) => walking_id = *id2,
                TermContents::Term(t) => return Some((walking_id, Some(t))),
            }
        }
        println!(
            "Warning: Excess depth, probably recursive variable reference, in {:?}",
            id
        );
        return None;
    }
    pub fn get_type_and_value(&self, id: TermVariableId) -> Option<&TermTypeAndValue> {
        self.unrolled_variable(id).and_then(|(a, b)| b)
    }
    pub fn get_value(&self, id: TermVariableId) -> Option<&TermValue> {
        self.get_type_and_value(id).map(|t| &t.value)
    }
    pub fn get_type_id(&self, id: TermVariableId) -> Option<TermVariableId> {
        self.get_type_and_value(id).map(|t| t.type_id)
    }
    pub fn is_sort(&self, id: TermVariableId) -> bool {
        matches!(
            self.get_type_and_value(id),
            Some(TermTypeAndValue {
                value: TermValue::Sort(_),
                ..
            })
        )
    }
    pub fn has_type_that_is_sort(&self, id: TermVariableId) -> bool {
        match self.get_type_and_value(id) {
            None => false,
            Some(TermTypeAndValue { type_id, .. }) => self.is_sort(*type_id),
        }
    }
    pub fn known_to_be_definitionally_equal(&self, a: TermVariableId, b: TermVariableId) -> bool {
        // let (a, av) =
        if a == b {
            return true;
        }
        false
        // // If they're different variables and both None, they don't count as the same
        // let Some(TermTypeAndValue { value: a, .. }) = &self.get_term(a).type_and_value else { return false; };
        // let Some(TermTypeAndValue { value: b, .. }) = &self.get_term(b).type_and_value else { return false; };
        // match (a, b) {
        //     (TermValue::VariableUsage(a), TermValue::VariableUsage(b)) => {
        //         // Variable usages have to be exactly the same variable, not merely same-term
        //         // (which would end up meaning "the variables are the same type")
        //         a == b
        //     }
        //     (TermValue::Sort(a), TermValue::Sort(b)) => a == b,
        //     (TermValue::Recursive(ak, ac), TermValue::Recursive(bk, bc)) => {
        //         ak == bk && iter::zip(ac, bc).all(|(a, b)| self.is_same_term(*a, *b))
        //     }
        //     _ => false,
        // }
    }
    pub fn known_to_be_definitionally_equal_with_substitution(
        &self,
        a: TermVariableId,
        b: TermVariableId,
        _replaced: TermVariableId,
        _replacement: TermVariableId,
    ) -> bool {
        if a == b {
            return true;
        }
        false
        // let Some(TermTypeAndValue { value: av, .. }) = &self.get_term(a).type_and_value else { return false; };
        // let Some(TermTypeAndValue { value: bv, .. }) = &self.get_term(b).type_and_value else { return false; };
        // match (av, bv) {
        //     (TermValue::VariableUsage(a), TermValue::VariableUsage(b)) if a == b => true,
        //     (_, TermValue::VariableUsage(b)) if *b == replaced => self.is_same_term(a, replacement),
        //     (TermValue::Sort(a), TermValue::Sort(b)) => a == b,
        //     (TermValue::Recursive(ak, ac), TermValue::Recursive(bk, bc)) => {
        //         ak == bk
        //             && iter::zip(ac, bc)
        //                 .all(|(a, b)| self.is_term_with_substitution(*a, *b, replaced, replacement))
        //     }
        //     _ => false,
        // }
    }
    pub fn local_validity(&self, id: TermVariableId) -> ElementaryDisproofsOfElementaryJudgments {
        let &TermContents::Term(TermTypeAndValue { type_id, ref value, .. }) = &self.get_term(id).contents else {
            // `Nothing` is not intrinsically invalid – it is only invalid to use it
            // as the type of anything but T, or as a subterm of any recursive term.
            // For references, we don't need to duplicate the work of checking whether the target is valid
            // or the work of checking whether our parent is valid based on what our value is
            return ElementaryDisproofsOfElementaryJudgments::NotAnActualTerm;
        };
        //
        // let Some(TermTypeAndValue { type_id: _, value: ty }) = &self.get_type_and_value(*type_id) else {
        //     // anything but Type has to have a type
        //     return matches!(value, TermValue::Sort(Sort::Type));
        // };

        match value {
            TermValue::VariableUsage(variable_id) => {
                ElementaryDisproofsOfElementaryJudgments::Variable {
                    type_not_known_to_be_definitionally_equal_to_binding_type: !self
                        .known_to_be_definitionally_equal(type_id, *variable_id),
                }
            }
            TermValue::Sort(sort) => match sort {
                Sort::Prop => ElementaryDisproofsOfElementaryJudgments::Prop {
                    type_is_not_t: !matches!(
                        self.get_value(type_id),
                        Some(TermValue::Sort(Sort::Type))
                    ),
                },
                Sort::Type => ElementaryDisproofsOfElementaryJudgments::Type {
                    has_type: self.get_value(type_id).is_some(),
                },
            },
            TermValue::Recursive(kind, child_ids) => {
                // let child_info = child_ids
                //     .each_ref()
                //     .map(|child| &self.get_term(*child).type_and_value);
                // let [Some(lhs), Some(rhs)] = child_info else { return false; };
                // let Some(TermTypeAndValue { value: lhs_type, .. }) = &self.get_term(lhs.type_id).type_and_value else {
                //     return false;
                // };

                use RecursiveTermKind::*;
                match kind {
                    ForAll => {
                        // if !matches!(lhs_type, TermValue::Sort(_)) {
                        //     return false;
                        // }
                        // match kind {
                        //     Lambda => {
                        //         let TermValue::Recursive(ForAll, [type_lhs_id, type_rhs_id]) = ty else { return false; };
                        //         self.is_same_term(*type_lhs_id, child_ids[0])
                        //             && self.is_same_term(*type_rhs_id, rhs.type_id)
                        //     }
                        //     ForAll => {
                        //         matches!(ty, TermValue::Sort(_))
                        //             && self.is_same_term(*type_id, rhs.type_id)
                        //     }
                        //     Apply => unreachable!(),
                        // }
                        let &[argument_type_id, return_type_id] = child_ids;
                        let type_not_known_to_be_definitionally_equal_to_return_type_type =
                            match self.get_type_id(return_type_id) {
                                None => true,
                                Some(return_type_type_id) => !self
                                    .known_to_be_definitionally_equal(type_id, return_type_type_id),
                            };
                        ElementaryDisproofsOfElementaryJudgments::ForAll {
                            argument_type_type_is_not_sort: !self
                                .has_type_that_is_sort(argument_type_id),
                            type_is_not_sort: !self.is_sort(type_id),
                            return_type_type_is_not_sort: !self
                                .has_type_that_is_sort(return_type_id),
                            type_not_known_to_be_definitionally_equal_to_return_type_type,
                        }
                    }
                    Lambda => {
                        let &[argument_type_id, body_id] = child_ids;
                        let (
                            type_is_not_forall,
                            argument_type_not_known_to_be_definitionally_equal_to_type_argument_type,
                            body_type_not_known_to_be_definitionally_equal_to_type_return_type,
                        ) = match self.get_value(type_id) {
                            None => (true, true, true),
                            Some(&TermValue::Recursive(
                                ForAll,
                                [type_argument_type_id, type_return_type_id],
                            )) => (
                                false,
                                !self.known_to_be_definitionally_equal(
                                    argument_type_id,
                                    type_argument_type_id,
                                ),
                                match self.get_type_id(body_id) {
                                    None => true,
                                    Some(body_type_id) => !self.known_to_be_definitionally_equal(
                                        body_type_id,
                                        type_return_type_id,
                                    ),
                                },
                            ),
                        };
                        ElementaryDisproofsOfElementaryJudgments::Lambda {
                            argument_type_type_is_not_sort: !self
                                .has_type_that_is_sort(argument_type_id),
                            type_is_not_forall,
                            argument_type_not_known_to_be_definitionally_equal_to_type_argument_type,
                            body_type_not_known_to_be_definitionally_equal_to_type_return_type,
                        }
                    }
                    Apply => {
                        let &[lhs_id, rhs_id] = child_ids;
                        match self.get_type_id(lhs_id).and_then (|lhs_type_id| self.get_value (lhs_type_id)) {
                            Some(&TermValue::Recursive(ForAll, [lhs_argument_type, lhs_return_type])) => ElementaryDisproofsOfElementaryJudgments::Apply {
                                lhs_type_is_not_forall: false,
                                lhs_argument_type_not_known_to_be_definitionally_equal_to_rhs_type: match self.get_type_id(rhs_id) {
                                    None => true,
                                    Some(rhs_type_id) => {
                                        !self.known_to_be_definitionally_equal(lhs_argument_type, rhs_type_id)
                                    }
                                },
                                type_not_known_to_be_definitionally_equal_to_substituted_lhs_return_type: self.known_to_be_definitionally_equal_with_substitution(
                                    type_id,
                                    lhs_return_type,
                                    lhs_argument_type,
                                    rhs_id,
                                ),
                            },
                            _ => ElementaryDisproofsOfElementaryJudgments::Apply {
                                lhs_type_is_not_forall: true,
                                lhs_argument_type_not_known_to_be_definitionally_equal_to_rhs_type: true,
                                type_not_known_to_be_definitionally_equal_to_substituted_lhs_return_type: true,
                            },
                        }
                    }
                }
            }
        }
    }

    pub fn with_sorts() -> Self {
        let mut result = Environment {
            terms: HashMap::new(),
        };
        let empty = result.create_term_variable();
        let ty = result.create_term_variable();
        let prop = result.create_term_variable();
        result.rename(empty, "NoType");
        result.rename(ty, "Type");
        result.rename(prop, "Prop");
        result.set(
            ty,
            Some(TermTypeAndValue {
                value: TermValue::Sort(Sort::Type),
                type_id: empty,
            }),
        );
        result.set(
            prop,
            Some(TermTypeAndValue {
                value: TermValue::Sort(Sort::Prop),
                type_id: ty,
            }),
        );
        result
    }
    pub fn create_term_variable(&mut self) -> TermVariableId {
        let id = TermVariableId(Uuid::new_v4());
        self.terms.insert(id, TermVariable::default());
        id
    }
    pub fn set_to_empty(&mut self, id: TermVariableId) {
        let contents = self.get_term_mut(id).type_and_value.take();
        let Some(TermTypeAndValue {
                     type_id,
                     value,
                 }) = contents else { return; };

        self.get_term_mut(type_id)
            .back_references
            .retain(|i| *i != id);

        match value {
            TermValue::VariableUsage(other_id) => {
                self.get_term_mut(other_id)
                    .back_references
                    .retain(|i| *i != id);
            }
            TermValue::Sort(_) => {}
            TermValue::Recursive(_, children) => {
                for child_id in children {
                    self.get_term_mut(child_id)
                        .back_references
                        .retain(|i| *i != id);
                }
            }
        }
    }
    fn populate_back_references(&mut self, id: TermVariableId) {
        let contents = self.get_term(id).type_and_value.clone();
        let Some(TermTypeAndValue {
                     type_id,
                     value,
                 }) = contents else { return; };
        self.get_term_mut(type_id).back_references.push(id);
        match value {
            TermValue::VariableUsage(other_id) => {
                self.get_term_mut(other_id).back_references.push(id);
            }
            TermValue::Sort(_) => {}
            TermValue::Recursive(_, children) => {
                for child_id in children {
                    self.get_term_mut(child_id).back_references.push(id);
                }
            }
        }
    }
    pub fn set(&mut self, id: TermVariableId, new_contents: Option<TermTypeAndValue>) {
        self.set_to_empty(id);
        self.get_term_mut(id).type_and_value = new_contents;
        self.populate_back_references(id);
    }
    pub fn set_to_copy_of(&mut self, id: TermVariableId, target: TermVariableId) {
        self.set(id, self.get_term(target).type_and_value.clone());
    }
    pub fn set_to_variable_usage(&mut self, id: TermVariableId, target: TermVariableId) {
        self.set(
            id,
            Some(TermTypeAndValue {
                value: TermValue::VariableUsage(target),
                type_id: target,
            }),
        );
    }
    pub fn set_to_new_recursive_term(&mut self, id: TermVariableId, kind: RecursiveTermKind) {
        let type_id = self.create_term_variable();
        let children = [self.create_term_variable(), self.create_term_variable()];
        self.set(
            id,
            Some(TermTypeAndValue {
                value: TermValue::Recursive(kind, children),
                type_id,
            }),
        );
    }
    pub fn rename(&mut self, id: TermVariableId, new_name: impl Into<String>) {
        self.get_term_mut(id).name = new_name.into();
    }
    pub fn fully_bound(&self, id: TermVariableId) -> bool {
        self.free_variables(id).is_empty()
    }
    pub fn free_variables(&self, id: TermVariableId) -> HashSet<TermVariableId> {
        let Some(value) = self.get_value(id) else { return HashSet::new(); };

        match value {
            TermValue::VariableUsage(other_id) => [*other_id].into_iter().collect(),
            TermValue::Sort(_) => HashSet::new(),
            TermValue::Recursive(kind, child_ids) => {
                let [l, mut r] = child_ids
                    .each_ref()
                    .map(|child_id| self.free_variables(*child_id));
                use RecursiveTermKind::*;
                if matches!(kind, Lambda | ForAll) {
                    r.remove(&child_ids[0]);
                }
                r.extend(l);
                r
            }
        }
    }

    pub fn term_variables(&self) -> impl Iterator<Item = (&TermVariableId, &TermVariable)> {
        self.terms.iter()
    }
}
