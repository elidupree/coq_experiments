use crate::term::RecursiveTermKind;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::{HashMap, HashSet};
use std::default::default;
use std::iter;
use uuid::Uuid;

#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Default, Debug,
)]
pub struct TermVariableId(pub Uuid);

#[derive(Default, Serialize, Deserialize, Debug)]
pub struct TermVariable {
    pub name: String,
    pub contents: TermContents,

    #[serde(skip)]
    pub parent: Option<TermVariableId>,
    #[serde(skip)]
    pub back_references: Vec<TermVariableId>,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
pub enum TermContents {
    Nothing,
    Reference(TermVariableId),
    Term(TermValue),
}

impl Default for TermContents {
    fn default() -> Self {
        TermContents::Nothing
    }
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
    Recursive {
        kind: RecursiveTermKind,
        child_ids: [TermVariableId; 2],
        type_id: TermVariableId,
    },
}

#[derive(Debug)]
pub struct Environment {
    terms: HashMap<TermVariableId, TermVariable>,
    id_of_t: TermVariableId,
}

#[derive(Debug)]
pub enum ElementaryDisproofsOfElementaryJudgments {
    TriviallyConsistent,
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
    pub fn is_invalid(&self) -> bool {
        match *self {
            ElementaryDisproofsOfElementaryJudgments::TriviallyConsistent => false,
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
    ) -> Option<(TermVariableId, Option<&TermValue>)> {
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
        None
    }
    pub fn get_value(&self, id: TermVariableId) -> Option<&TermValue> {
        self.unrolled_variable(id).and_then(|(_id, v)| v)
    }
    pub fn get_type_id(&self, id: TermVariableId) -> Option<TermVariableId> {
        self.get_value(id).and_then(|t| match *t {
            TermValue::Sort(Sort::Type) => None,
            TermValue::Sort(Sort::Prop) => Some(self.id_of_t),
            TermValue::VariableUsage(target) => Some(target),
            TermValue::Recursive { type_id, .. } => Some(type_id),
        })
    }
    pub fn is_sort(&self, id: TermVariableId) -> bool {
        matches!(self.get_value(id), Some(TermValue::Sort(_)))
    }
    pub fn has_type_that_is_sort(&self, id: TermVariableId) -> bool {
        match self.get_type_id(id) {
            None => false,
            Some(type_id) => self.is_sort(type_id),
        }
    }
    pub fn known_to_be_definitionally_equal(&self, a: TermVariableId, b: TermVariableId) -> bool {
        // let (a, av) =
        if matches!((self.unrolled_variable(a), self.unrolled_variable(b)), (Some((a,_)),Some((b,_))) if a == b)
        {
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
        if matches!((self.unrolled_variable(a), self.unrolled_variable(b)), (Some((a,_)),Some((b,_))) if a == b)
        {
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
        let TermContents::Term(value) = &self.get_term(id).contents else {
            // `Nothing` is not intrinsically invalid – it is only invalid to use it
            // as the type of anything but T, or as a subterm of any recursive term.
            // For references, we don't need to duplicate the work of checking whether the target is valid
            // or the work of checking whether our parent is valid based on what our value is
            return ElementaryDisproofsOfElementaryJudgments::TriviallyConsistent;
        };
        //
        // let Some(TermTypeAndValue { type_id: _, value: ty }) = &self.get_type_and_value(*type_id) else {
        //     // anything but Type has to have a type
        //     return matches!(value, TermValue::Sort(Sort::Type));
        // };

        match value {
            TermValue::VariableUsage(_) => {
                // the type is *defined* to be equal to the type of the variable binding
                ElementaryDisproofsOfElementaryJudgments::TriviallyConsistent
            }
            TermValue::Sort(_) => {
                // the type (or lack thereof) is immediately known by the axioms
                ElementaryDisproofsOfElementaryJudgments::TriviallyConsistent
            }
            &TermValue::Recursive {
                kind,
                child_ids,
                type_id,
            } => {
                use RecursiveTermKind::*;
                match kind {
                    ForAll => {
                        let [argument_type_id, return_type_id] = child_ids;
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
                        let [argument_type_id, body_id] = child_ids;
                        let (
                            type_is_not_forall,
                            argument_type_not_known_to_be_definitionally_equal_to_type_argument_type,
                            body_type_not_known_to_be_definitionally_equal_to_type_return_type,
                        ) = match self.get_value(type_id) {
                            Some(&TermValue::Recursive {
                                kind: ForAll,
                                child_ids: [type_argument_type_id, type_return_type_id],
                                ..
                            }) => (
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
                            _ => (true, true, true),
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
                        let [lhs_id, rhs_id] = child_ids;
                        match self.get_type_id(lhs_id).and_then(|lhs_type_id| self.get_value(lhs_type_id)) {
                            Some(&TermValue::Recursive {
                                kind: ForAll,
                                child_ids: [lhs_argument_type, lhs_return_type],
                                ..
                            }) => ElementaryDisproofsOfElementaryJudgments::Apply {
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
            id_of_t: default(),
        };
        result.id_of_t = result.create_term_variable();
        let prop = result.create_term_variable();
        result.rename(result.id_of_t, "Type");
        result.rename(prop, "Prop");
        result.set(
            result.id_of_t,
            TermContents::Term(TermValue::Sort(Sort::Type)),
        );
        result.set(prop, TermContents::Term(TermValue::Sort(Sort::Prop)));
        result
    }
    pub fn create_term_variable(&mut self) -> TermVariableId {
        let id = TermVariableId(Uuid::new_v4());
        self.terms.insert(id, TermVariable::default());
        id
    }
    fn remove_parent(&mut self, id: TermVariableId) {
        assert!(self.get_term_mut(id).parent.take().is_some());
    }
    fn add_parent(&mut self, id: TermVariableId, parent: TermVariableId) {
        assert!(self.get_term_mut(id).parent.replace(parent).is_none());
    }
    pub fn set_to_empty(&mut self, id: TermVariableId) {
        let contents = std::mem::take(&mut self.get_term_mut(id).contents);
        let value = match contents {
            TermContents::Nothing => return,
            TermContents::Reference(target) => {
                self.get_term_mut(target)
                    .back_references
                    .retain(|i| *i != id);
                return;
            }
            TermContents::Term(t) => t,
        };

        match value {
            TermValue::VariableUsage(target) => {
                self.get_term_mut(target)
                    .back_references
                    .retain(|i| *i != id);
            }
            TermValue::Sort(_) => {}
            TermValue::Recursive {
                child_ids, type_id, ..
            } => {
                for child_id in child_ids {
                    self.remove_parent(child_id);
                }
                self.remove_parent(type_id);
            }
        }
    }
    fn populate_back_references(&mut self, id: TermVariableId) {
        let contents = self.get_term(id).contents.clone();
        let value = match contents {
            TermContents::Nothing => return,
            TermContents::Reference(target) => {
                self.get_term_mut(target).back_references.push(id);
                return;
            }
            TermContents::Term(t) => t,
        };

        match value {
            TermValue::VariableUsage(target) => {
                self.get_term_mut(target).back_references.push(id);
            }
            TermValue::Sort(Sort::Prop) => {}
            TermValue::Sort(Sort::Type) => self.id_of_t = id,
            TermValue::Recursive {
                child_ids, type_id, ..
            } => {
                for child_id in child_ids {
                    self.add_parent(child_id, id);
                }
                self.add_parent(type_id, id);
            }
        }
    }
    fn set(&mut self, id: TermVariableId, new_contents: TermContents) {
        self.set_to_empty(id);
        self.get_term_mut(id).contents = new_contents;
        self.populate_back_references(id);
    }
    pub fn set_to_reference_to(&mut self, id: TermVariableId, target: TermVariableId) {
        self.set(id, TermContents::Reference(target));
    }
    pub fn set_to_variable_usage(&mut self, id: TermVariableId, target: TermVariableId) {
        self.set(id, TermContents::Term(TermValue::VariableUsage(target)));
    }
    pub fn set_to_new_recursive_term(&mut self, id: TermVariableId, kind: RecursiveTermKind) {
        let type_id = self.create_term_variable();
        let child_ids = [self.create_term_variable(), self.create_term_variable()];
        self.set(
            id,
            TermContents::Term(TermValue::Recursive {
                kind,
                child_ids,
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
            TermValue::Recursive {
                kind, child_ids, ..
            } => {
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
    pub fn context(&self, id: TermVariableId) -> impl Iterator<Item = TermVariableId> + '_ {
        let mut walking_id = id;
        iter::from_fn(move || loop {
            walking_id = self.get_term(walking_id).parent?;
            if let Some(TermValue::Recursive {
                kind, child_ids, ..
            }) = self.get_value(walking_id)
            {
                use RecursiveTermKind::*;
                if matches!(kind, Lambda | ForAll) {
                    return Some(child_ids[0]);
                }
            }
        })
    }

    pub fn term_variables(&self) -> impl Iterator<Item = (&TermVariableId, &TermVariable)> {
        self.terms.iter()
    }
}

impl Serialize for Environment {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.terms.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Environment {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let terms = HashMap::<TermVariableId, TermVariable>::deserialize(deserializer)?;
        let mut result = Environment {
            terms,
            id_of_t: default(),
        };
        for id in result.terms.keys().copied().collect::<Vec<_>>() {
            result.populate_back_references(id);
        }
        Ok(result)
    }
}
