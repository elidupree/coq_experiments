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
    pub type_and_value: Option<TermTypeAndValue>,

    pub back_references: Vec<TermVariableId>,
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

impl Environment {
    pub fn get_term(&self, id: TermVariableId) -> &TermVariable {
        self.terms.get(&id).unwrap()
    }
    fn get_term_mut(&mut self, id: TermVariableId) -> &mut TermVariable {
        self.terms.get_mut(&id).unwrap()
    }
    pub fn is_same_term(&self, a: TermVariableId, b: TermVariableId) -> bool {
        if a == b {
            return true;
        }
        // If they're different variables and both None, they don't count as the same
        let Some(TermTypeAndValue { value: a, .. }) = &self.get_term(a).type_and_value else { return false; };
        let Some(TermTypeAndValue { value: b, .. }) = &self.get_term(b).type_and_value else { return false; };
        match (a, b) {
            (TermValue::VariableUsage(a), TermValue::VariableUsage(b)) => {
                // Variable usages have to be exactly the same variable, not merely same-term
                // (which would end up meaning "the variables are the same type")
                a == b
            }
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
        if a == b {
            return true;
        }
        let Some(TermTypeAndValue { value: av, .. }) = &self.get_term(a).type_and_value else { return false; };
        let Some(TermTypeAndValue { value: bv, .. }) = &self.get_term(b).type_and_value else { return false; };
        match (av, bv) {
            (TermValue::VariableUsage(a), TermValue::VariableUsage(b)) if a == b => true,
            (_, TermValue::VariableUsage(b)) if *b == replaced => self.is_same_term(a, replacement),
            (TermValue::Sort(a), TermValue::Sort(b)) => a == b,
            (TermValue::Recursive(ak, ac), TermValue::Recursive(bk, bc)) => {
                ak == bk
                    && iter::zip(ac, bc)
                        .all(|(a, b)| self.is_term_with_substitution(*a, *b, replaced, replacement))
            }
            _ => false,
        }
    }
    pub fn locally_valid(&self, id: TermVariableId) -> bool {
        let Some(TermTypeAndValue { type_id, value, .. }) = &self.get_term(id).type_and_value else {
            // `None` is not intrinsically invalid – it is only invalid to use it
            // as the type of anything but T, or as a subterm of any recursive term
            return true;
        };

        let Some(TermTypeAndValue { type_id: _, value: ty }) = &self.get_term(*type_id).type_and_value else {
            return matches!(value, TermValue::Sort(Sort::Type));
        };

        match value {
            TermValue::VariableUsage(variable_id) => self.is_same_term(*type_id, *variable_id),
            TermValue::Sort(sort) => match sort {
                Sort::Prop => matches!(ty, TermValue::Sort(Sort::Type)),
                Sort::Type => false,
            },
            TermValue::Recursive(kind, child_ids) => {
                let child_info = child_ids
                    .each_ref()
                    .map(|child| &self.get_term(*child).type_and_value);
                let [Some(lhs), Some(rhs)] = child_info else { return false; };
                let Some(TermTypeAndValue { value: lhs_type, .. }) = &self.get_term(lhs.type_id).type_and_value else {
                    return false;
                };

                use RecursiveTermKind::*;
                match kind {
                    Lambda | ForAll => {
                        if !matches!(lhs_type, TermValue::Sort(_)) {
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
                self.get_term_mut(type_id).back_references.push(other_id);
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
        let Some(TermTypeAndValue {
                     value, ..
                 }) = &self.get_term(id).type_and_value else { return HashSet::new(); };

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
