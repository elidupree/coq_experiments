use crate::introspective_calculus::proof_hierarchy::Proof;
use crate::introspective_calculus::{Atom, RWMFormula, Substitutions};
use crate::utils::todo;
use std::collections::{BTreeSet, HashMap, HashSet};

// "form_classes" are equivalence classes of formulas with metavariables;
// a formula A "matches" a form_class F if there is some member of F where F[x..:=B..] is exactly A
// some variables may be ignored (e.g. the form_class [const A B] also has a member [A], and only A need be noted in the match)

struct FormulaWithPremises {
    formula: RWMFormula,
    premises: BTreeSet<RWMFormula>,
}

// for some formula, the way that formula matches a particular form_class
struct FormClassMatch {
    form_class: EquivalenceClassId,
    relevant_variable_values: Substitutions,
}

struct EquivalenceClassId(FormulaWithPremises);

enum EquivalenceClassMember {
    Atom(Atom),
    Metavariable(String),
    Application([EquivalenceClassId; 2]),
}

struct EquivalenceClass {
    members: HashSet<EquivalenceClassMember>,

    // to match things with the form_class AB, we need to recognize the form_class A and the form_class B individually
    important_superforms: HashSet<EquivalenceClassId>,
    important_subforms: HashSet<EquivalenceClassId>,

    applications_involving_me: HashSet<EquaivalenceClassId>,

    // goal_sides_of_this_form_class: HashSet<FormulaWithPremises>,
    important_form_classes_this_matches: HashSet<FormClassMatch>,
    formulas_that_match_this_form_class: HashSet<EquivalenceClassId>,

    // each class with premises implicitly incorporates all members of all classes that share an element with the present class and have a subset of its premises.
    // the ones with superset of premises always (implicitly) contain superset of formulas
    overlapping_classes_with_subset_premises: HashSet<EquivalenceClassId>,
    overlapping_classes_with_superset_premises: HashSet<EquivalenceClassId>,
}

enum FormulaWithPremisesEntry {
    RepresentativeOfClass(EquivalenceClass),
    DelegatesTo(RWMFormula),
}
struct FormulaWithPremisesEntry {}

struct Aggregator {
    goals: uhh,
}

impl Aggregator {
    pub fn discover_proof(&mut self, proof: Proof) {
        let sides = proof.conclusion().as_eq_sides().unwrap();
        // find the representatives; if they are not already equal, equate them; the process of equation must update applications' form_class-matching records
    }

    pub fn merge_classes(&mut self, classes: [EquivalenceClassId; 2]) {
        // merge formulas_that_match_this_form_class, update back references
        // merge important_form_classes_this_matches, update back references
        // merge applications_involving_me, update back references

        // I now have more important_form_classes_this_matches, so members of applications_involving_me may gain more important_form_classes_this_matches
    }

    pub fn form_class_match_discovered(
        &mut self,
        class: EquivalenceClassId,
        form_class_match: FormClassMatch,
    ) {
        // classes x, y, xy
        // form_class A
        // discovered x<A, examine the class xy...
        // need to check if there's form_classes B, AB with y<B
        // i.e. A.important_superforms_by_sibling(y)... but, we need to check whether they match y...
        class.important_forms_this_matches.insert(form_class_match);
        form_class_match
            .form_class
            .formulas_that_match_this_form
            .insert(class);

        for application_involving_me in todo::<&mut EquivalenceClass, _>(class) {
            let [x, y] = application_involving_me;
            for superform in &form_class_match.form_class.important_superforms {
                if let Some(y_match) = y.matches(superform.sibling_of(form_class_match.form_class))
                {
                    if let Some(merged) = merge_matches(superform, form_class_match, y_match) {
                        self.form_class_match_discovered(application_involving_me, merged);
                    }
                }
            }
        }

        for goal in "goals of which this class is a side" {
            if goal.other_side.matches.contains(form_class_match) {
                goal.solved();
            } else {
                goal.this_side.matches.insert(form_class_match);
            }
        }
    }
}
