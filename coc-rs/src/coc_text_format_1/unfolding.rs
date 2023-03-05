use crate::coc_text_format_1::{Abstraction, AbstractionKind, Formula, GlobalContext};
use std::collections::HashMap;
use std::mem;

pub enum SubformulaPathStep {
    Left,
    Right,
}

impl Formula {
    pub fn contains_free_usage(&self, name: &str) -> bool {
        match self {
            Formula::Prop => false,
            Formula::Usage(other) => other == name,
            Formula::Hole => false,
            Formula::Abstraction(a) => {
                a.parameter_type.contains_free_usage(name)
                    || (a.parameter_name != name && a.body.contains_free_usage(name))
            }
            Formula::Apply(children) => {
                children[0].contains_free_usage(name) || children[1].contains_free_usage(name)
            }
        }
    }
    pub fn substitute(&mut self, replaced: &str, replacement: &Formula) {
        match self {
            Formula::Usage(name) => {
                if name == replaced {
                    *self = replacement.clone();
                }
            }
            Formula::Abstraction(a) => {
                a.parameter_type.substitute(replaced, replacement);
                if replacement.contains_free_usage(&a.parameter_name) {
                    let mut new_name = format!("{}'", a.parameter_name);
                    while replacement.contains_free_usage(&new_name)
                        || a.body.contains_free_usage(&new_name)
                    {
                        new_name = format!("{}'", new_name)
                    }
                    a.body
                        .substitute(&a.parameter_name, &Formula::Usage(new_name.clone()));
                    a.parameter_name = new_name;
                }
                a.body.substitute(replaced, replacement);
            }
            Formula::Apply(children) => {
                for child in &mut **children {
                    child.substitute(replaced, replacement);
                }
            }
            _ => {}
        }
    }

    pub fn subformula(&self, location: &[SubformulaPathStep]) -> &Formula {
        match (self, location.split_first()) {
            (_, None) => self,

            (Formula::Apply(children), Some((first, rest))) => match first {
                SubformulaPathStep::Left => children[0].subformula(rest),
                SubformulaPathStep::Right => children[1].subformula(rest),
            },

            (Formula::Abstraction(abstraction), Some((first, rest))) => match first {
                SubformulaPathStep::Left => abstraction.parameter_type.subformula(rest),
                SubformulaPathStep::Right => abstraction.body.subformula(rest),
            },

            _ => panic!("invalid subformula path"),
        }
    }

    pub fn unfold(
        &mut self,
        location: &[SubformulaPathStep],
        globals: &GlobalContext,
    ) -> Result<(), &'static str> {
        match (&mut *self, location.split_first()) {
            (Formula::Apply(children), None) => {
                let [f, v] = &mut **children;
                let (body, parameter_name) = match f {
                    Formula::Abstraction(f) => {
                        (mem::take(&mut f.body), mem::take(&mut f.parameter_name))
                    }
                    Formula::Usage(n) => {
                        let Some (Formula::Abstraction(f)) =  globals.definitions.get(&**n) else {return Err ("invalid unfold path")};
                        (f.body.clone(), f.parameter_name.clone())
                    }
                    _ => return Err("invalid unfold path"),
                };
                let v = mem::take(v);

                *self = body;
                self.substitute(&parameter_name, &v);
            }

            (Formula::Apply(children), Some((first, rest))) => {
                let child = match first {
                    SubformulaPathStep::Left => &mut children[0],
                    SubformulaPathStep::Right => &mut children[1],
                };
                child.unfold(rest, globals)?;
            }

            (Formula::Abstraction(abstraction), Some((first, rest))) => {
                let child = match first {
                    SubformulaPathStep::Left => &mut abstraction.parameter_type,
                    SubformulaPathStep::Right => &mut abstraction.body,
                };
                child.unfold(rest, globals)?;
            }

            _ => return Err("invalid unfold path"),
        }
        Ok(())
    }

    pub fn favored_crease_in_closed_formula<'a>(
        &'a self,
        globals: &GlobalContext,
        mut context_variables: Vec<&'a str>,
    ) -> Option<Vec<SubformulaPathStep>> {
        match self {
            Formula::Prop => None,
            Formula::Usage(name) => {
                if context_variables.contains(&&**name) {
                    None
                } else {
                    globals
                        .definitions
                        .get(name)
                        .unwrap()
                        .favored_crease_in_closed_formula(globals, Vec::new())
                }
            }
            Formula::Hole => None,
            Formula::Abstraction(a) => {
                context_variables.push(&a.parameter_name);
                let mut result = a
                    .body
                    .favored_crease_in_closed_formula(globals, context_variables)?;
                result.insert(0, SubformulaPathStep::Right);
                Some(result)
            }
            Formula::Apply(children) => {
                if matches!(&children[0], Formula::Abstraction(_))
                    || matches!(&children[0], Formula::Usage(name) if matches!(globals.definitions.get(name), Some(Formula::Abstraction(_))))
                {
                    Some(Vec::new())
                } else {
                    let mut result =
                        children[0].favored_crease_in_closed_formula(globals, context_variables)?;
                    result.insert(0, SubformulaPathStep::Left);
                    Some(result)
                }
            }
        }
    }

    pub fn naive_type<'a>(
        &'a self,
        globals: &GlobalContext,
        mut context: HashMap<&'a str, &'a Formula>,
    ) -> Formula {
        match self {
            Formula::Prop => Formula::Prop,
            Formula::Usage(name) => {
                if let Some(&ty) = context.get(&**name) {
                    ty.clone()
                } else {
                    globals
                        .definitions
                        .get(name)
                        .unwrap()
                        .naive_type(globals, context)
                }
            }
            Formula::Hole => Formula::Hole,
            Formula::Abstraction(a) => match a.kind {
                AbstractionKind::Lambda => {
                    context.insert(&*a.parameter_name, &a.parameter_type);
                    Formula::Abstraction(Box::new(Abstraction {
                        kind: AbstractionKind::ForAll,
                        parameter_name: a.parameter_name.clone(),
                        parameter_type: a.parameter_type.clone(),
                        body: a.body.naive_type(globals, context),
                    }))
                }
                AbstractionKind::ForAll => Formula::Prop,
            },
            Formula::Apply(children) => Formula::Apply(Box::new([
                children[0].naive_type(globals, context),
                children[1].clone(),
            ])),
        }
    }

    // pub fn shorten_by_making_globals(
    //     &mut self,
    //     globals: &mut GlobalContext,
    // ) {}
}
