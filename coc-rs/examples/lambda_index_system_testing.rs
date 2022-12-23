#![feature(array_methods)]
#![feature(array_zip)]

use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::rc::Rc;
use std::{iter, mem};

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct OpaqueIndexRepresentative(usize);

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
struct IndexClassId(usize);

#[derive(Debug, Eq, PartialEq)]
enum IndexRepresentativeInfo {
    MainOfClass(IndexClassId),
    DelegatedTo(OpaqueIndexRepresentative),
}

#[derive(Debug)]
struct IndexClassInfo {
    main_representative: OpaqueIndexRepresentative,
    must_not_equal: Vec<IndexClassId>,
}

#[derive(Default, Debug)]
pub struct IdentifiableIndices {
    representatives: Vec<IndexRepresentativeInfo>,
    classes: Vec<IndexClassInfo>,
}

impl IdentifiableIndices {
    pub fn new() -> Self {
        Self::default()
    }
    fn get_main_of_class(
        &mut self,
        r: OpaqueIndexRepresentative,
    ) -> (OpaqueIndexRepresentative, IndexClassId) {
        match self.representatives[r.0] {
            IndexRepresentativeInfo::MainOfClass(class_id) => (r, class_id),
            IndexRepresentativeInfo::DelegatedTo(next) => {
                let (main, class_id) = self.get_main_of_class(next);
                self.representatives[r.0] = IndexRepresentativeInfo::DelegatedTo(next);
                (main, class_id)
            }
        }
    }
    fn get_class_id(&mut self, r: OpaqueIndexRepresentative) -> IndexClassId {
        self.get_main_of_class(r).1
    }
    pub fn make_new_index(&mut self) -> OpaqueIndexRepresentative {
        self.representatives
            .push(IndexRepresentativeInfo::MainOfClass(IndexClassId(
                self.classes.len(),
            )));
        self.classes.push(IndexClassInfo {
            main_representative: OpaqueIndexRepresentative(self.representatives.len() - 1),
            must_not_equal: vec![],
        });
        OpaqueIndexRepresentative(self.representatives.len() - 1)
    }
    fn move_backrefs(&mut self, class_id: IndexClassId, new_id: IndexClassId) {
        self.representatives[self.classes[class_id.0].main_representative.0] =
            IndexRepresentativeInfo::MainOfClass(new_id);
        for exclusion in self.classes[class_id.0].must_not_equal.clone() {
            for back_reference in &mut self.classes[exclusion.0].must_not_equal {
                if *back_reference == class_id {
                    *back_reference = new_id
                }
            }
            self.classes[exclusion.0].must_not_equal.sort();
            self.classes[exclusion.0].must_not_equal.dedup();
        }
    }
    fn validate(&self) {
        for (index, class) in self.classes.iter().enumerate() {
            assert_eq!(
                self.representatives[class.main_representative.0],
                IndexRepresentativeInfo::MainOfClass(IndexClassId(index))
            );
            for exclusion in &class.must_not_equal {
                assert_ne!(exclusion.0, index);
                assert!(self.classes[exclusion.0]
                    .must_not_equal
                    .contains(&IndexClassId(index)))
            }
        }
    }
    pub fn try_identify(
        &mut self,
        r1: OpaqueIndexRepresentative,
        r2: OpaqueIndexRepresentative,
    ) -> Result<(), ()> {
        self.validate();
        let mut c1 = self.get_class_id(r1);
        let mut c2 = self.get_class_id(r2);
        if c1 == c2 {
            return Ok(());
        }
        if c2 < c1 {
            mem::swap(&mut c1, &mut c2);
        }
        if self.classes[c1.0].must_not_equal.contains(&c2) {
            return Err(());
        }
        let cl = IndexClassId(self.classes.len() - 1);
        self.move_backrefs(c2, c1);
        let taken = self.classes[c2.0].must_not_equal.clone();
        self.classes[c1.0].must_not_equal.extend_from_slice(&taken);

        if c2 != cl {
            self.move_backrefs(cl, c2);
        }
        self.representatives[self.classes[c2.0].main_representative.0] =
            IndexRepresentativeInfo::DelegatedTo(self.classes[c1.0].main_representative);
        // dbg!((
        //     r1,
        //     r2,
        //     c1,
        //     c2,
        //     cl,
        //     self.classes.len(),
        //     &self.classes[c1.0].must_not_equal
        // ));

        self.classes[c1.0].must_not_equal.sort();
        self.classes[c1.0].must_not_equal.dedup();
        self.classes.swap_remove(c2.0);

        // dbg!((self.classes.len(), &self.classes[c1.0].must_not_equal));
        self.validate();
        Ok(())
    }
    pub fn try_exclude(
        &mut self,
        r1: OpaqueIndexRepresentative,
        r2: OpaqueIndexRepresentative,
    ) -> Result<(), ()> {
        let c1 = self.get_class_id(r1);
        let c2 = self.get_class_id(r2);
        if c1 == c2 {
            return Err(());
        }
        if self.classes[c1.0].must_not_equal.contains(&c2) {
            return Ok(());
        }
        self.classes[c1.0].must_not_equal.push(c2);
        self.classes[c2.0].must_not_equal.push(c1);
        Ok(())
    }
    pub fn short_name(&mut self, r: OpaqueIndexRepresentative) -> usize {
        self.get_class_id(r).0
    }
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
enum DeBruijnExpression {
    Variable(usize),
    Apply([Rc<DeBruijnExpression>; 2]),
    Lambda(Rc<DeBruijnExpression>),
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
enum Expression {
    Variable(OpaqueIndexRepresentative),
    Apply([Rc<Expression>; 2]),
    Lambda(OpaqueIndexRepresentative, Rc<Expression>),
}

impl Debug for DeBruijnExpression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            DeBruijnExpression::Variable(v) => v.fmt(f),
            DeBruijnExpression::Apply(children) => {
                f.write_str("(")?;
                children[0].fmt(f)?;
                f.write_str(" ")?;
                children[1].fmt(f)?;
                f.write_str(")")?;
                Ok(())
            }
            DeBruijnExpression::Lambda(body) => {
                f.write_str("λ")?;
                body.fmt(f)?;
                Ok(())
            }
        }
    }
}

impl Debug for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Variable(v) => v.0.fmt(f),
            Expression::Apply(children) => {
                f.write_str("(")?;
                children[0].fmt(f)?;
                f.write_str(" ")?;
                children[1].fmt(f)?;
                f.write_str(")")?;
                Ok(())
            }
            Expression::Lambda(v, body) => {
                f.write_str("λ")?;
                v.0.fmt(f)?;
                f.write_str(",")?;
                body.fmt(f)?;
                Ok(())
            }
        }
    }
}

impl DeBruijnExpression {
    fn all_short(depth: usize, max_overflow: usize) -> Vec<Rc<DeBruijnExpression>> {
        if depth == 0 {
            (0..max_overflow)
                .map(|i| Rc::new(DeBruijnExpression::Variable(i)))
                .collect()
        } else {
            let mut result = Vec::new();
            let possible_children = Self::all_short(depth - 1, max_overflow);
            for child1 in &possible_children {
                for child2 in &possible_children {
                    result.push(Rc::new(DeBruijnExpression::Apply([
                        child1.clone(),
                        child2.clone(),
                    ])));
                }
            }
            for body in Self::all_short(depth - 1, max_overflow + 1) {
                result.push(Rc::new(DeBruijnExpression::Lambda(body)));
            }
            result
        }
    }

    fn max_overflow(&self) -> usize {
        match self {
            DeBruijnExpression::Variable(v) => *v + 1,
            DeBruijnExpression::Apply(children) => {
                children.iter().map(|c| c.max_overflow()).max().unwrap()
            }
            DeBruijnExpression::Lambda(body) => body.max_overflow().saturating_sub(1),
        }
    }
}

impl Expression {
    fn to_de_bruijn(
        &self,
        variables: &HashMap<OpaqueIndexRepresentative, usize>,
    ) -> Rc<DeBruijnExpression> {
        Rc::new(match self {
            Expression::Variable(v) => DeBruijnExpression::Variable(variables[v]),
            Expression::Apply(children) => {
                DeBruijnExpression::Apply(children.each_ref().map(|c| c.to_de_bruijn(variables)))
            }
            Expression::Lambda(v, body) => {
                let new_variables: HashMap<_, _> = iter::once((*v, 0))
                    .chain(
                        variables
                            .iter()
                            .filter(|&(k, _)| k != v)
                            .map(|(&v, &i)| (v, i + 1)),
                    )
                    .collect();
                DeBruijnExpression::Lambda(body.to_de_bruijn(&new_variables))
            }
        })
    }
    fn substitute(
        &self,
        substitutions: &HashMap<OpaqueIndexRepresentative, Rc<Expression>>,
    ) -> Rc<Expression> {
        match self {
            Expression::Variable(v) => {
                if let Some(replaced) = substitutions.get(v) {
                    replaced.clone()
                } else {
                    Rc::new(Expression::Variable(*v))
                }
            }
            Expression::Apply(children) => Rc::new(Expression::Apply(
                children.each_ref().map(|c| c.substitute(substitutions)),
            )),
            Expression::Lambda(v, body) => {
                Rc::new(if substitutions.contains_key(v) {
                    // need a special case to support shadowing
                    let new_substitutions = substitutions
                        .iter()
                        .filter(|(k, _)| *k != v)
                        .map(|(a, b)| (a.clone(), b.clone()))
                        .collect();
                    Expression::Lambda(*v, body.substitute(&new_substitutions))
                } else {
                    Expression::Lambda(*v, body.substitute(substitutions))
                })
            }
        }
    }
    fn all_single_step_beta_reductions(&self) -> Vec<Rc<Expression>> {
        let mut result = Vec::new();
        match self {
            Expression::Variable(_v) => {}
            Expression::Apply(children) => {
                if let Expression::Lambda(v, body) = &*children[0] {
                    let substitutions: HashMap<_, _> =
                        iter::once((*v, children[1].clone())).collect();
                    result.push(body.substitute(&substitutions));
                }
                for reduction in children[0].all_single_step_beta_reductions() {
                    result.push(Rc::new(Expression::Apply([reduction, children[1].clone()])));
                }
                for reduction in children[1].all_single_step_beta_reductions() {
                    result.push(Rc::new(Expression::Apply([children[0].clone(), reduction])));
                }
            }
            Expression::Lambda(v, body) => {
                for reduction in body.all_single_step_beta_reductions() {
                    result.push(Rc::new(Expression::Lambda(*v, reduction)));
                }
            }
        }
        result
    }
    fn identify_with(
        &self,
        other: &Expression,
        indices: &mut IdentifiableIndices,
    ) -> Result<(), ()> {
        match (self, other) {
            (Expression::Variable(a), Expression::Variable(b)) => indices.try_identify(*a, *b),
            (Expression::Apply(cs1), Expression::Apply(cs2)) => {
                for (a, b) in cs1.each_ref().zip(cs2.each_ref()) {
                    a.identify_with(b, indices)?;
                }
                Ok(())
            }
            (Expression::Lambda(v1, body1), Expression::Lambda(v2, body2)) => {
                indices.try_identify(*v1, *v2)?;
                body1.identify_with(body2, indices)?;
                Ok(())
            }
            _ => panic!("identify_with must be used on expressions with identical structure"),
        }
    }
}

#[derive(Default)]
struct CanonicalExpressions {
    indices: IdentifiableIndices,
    expressions: HashMap<DeBruijnExpression, Rc<Expression>>,
}

impl CanonicalExpressions {
    fn make_fresh_canonical_part(
        &mut self,
        source: &DeBruijnExpression,
        variable_indices: &[OpaqueIndexRepresentative],
        canonical_may_be_available: bool,
    ) -> Rc<Expression> {
        if canonical_may_be_available && source.max_overflow() == 0 {
            return self.require_canonical_form(source, variable_indices);
        }

        Rc::new(match source {
            &DeBruijnExpression::Variable(v) => {
                // When we find a free variable, we know it must be distinct from all bindings BETWEEN
                // the variable binding and use-site (but may be shadowed by bindings after the use-site)
                let i = variable_indices[v];
                for &j in &variable_indices[..v] {
                    // all of these indices are fresh and haven't been identified with anything yet,
                    // so exclusion should never fail
                    self.indices.try_exclude(i, j).unwrap();
                }
                Expression::Variable(i)
            }
            DeBruijnExpression::Apply(children) => Expression::Apply(
                children
                    .each_ref()
                    .map(|c| self.make_fresh_canonical_part(c, variable_indices, true)),
            ),
            DeBruijnExpression::Lambda(body) => {
                let index = self.indices.make_new_index();
                let new_indices: Vec<_> = iter::once(index)
                    .chain(variable_indices.iter().copied())
                    .collect();

                Expression::Lambda(
                    index,
                    self.make_fresh_canonical_part(body, &new_indices, true),
                )
            }
        })
    }
    fn require_canonical_form(
        &mut self,
        source: &DeBruijnExpression,
        variable_indices: &[OpaqueIndexRepresentative],
    ) -> Rc<Expression> {
        assert_eq!(source.max_overflow(), 0);
        if let Some(precalculated) = self.expressions.get(&source) {
            return precalculated.clone();
        }

        let result = self.make_fresh_canonical_part(source, variable_indices, false);
        //dbg!((source, &result));
        assert_eq!(&*result.to_de_bruijn(&HashMap::new()), source);
        self.expressions.insert(source.clone(), result.clone());
        result
    }

    fn identify_with_canonical_form(&mut self, expression: &Expression) -> Result<(), ()> {
        let de = expression.to_de_bruijn(&HashMap::new());
        let canonical = self.require_canonical_form(&de, &[]);
        expression.identify_with(&canonical, &mut self.indices)
    }
}

fn main() {
    let mut indices = IdentifiableIndices::new();
    let a = indices.make_new_index();
    let b = indices.make_new_index();
    println!("{}, {}", indices.short_name(a), indices.short_name(b));
    println!("{:?}", indices.try_identify(a, b));
    println!("{}, {}", indices.short_name(a), indices.short_name(b));
    let c = indices.make_new_index();
    println!("{:?}", indices);
    println!("{:?}", (c, indices.get_main_of_class(c)));
    println!("{:?}", indices.try_exclude(a, b));
    println!("{:?}", indices.try_exclude(a, c));
    println!("{:?}", indices.try_identify(b, c));
    println!(
        "{:?}",
        (
            indices.short_name(a),
            indices.short_name(b),
            indices.short_name(c)
        )
    );

    let mut canonical = CanonicalExpressions::default();
    for max_depth in 0..6 {
        for expression in DeBruijnExpression::all_short(max_depth, 0) {
            println!("{}, {:?}", canonical.indices.classes.len(), expression);
            let expression = canonical.require_canonical_form(&*expression, &[]);
            for reduction in expression.all_single_step_beta_reductions() {
                if let Err(_) = canonical.identify_with_canonical_form(&reduction) {
                    println!("{:?}", &expression);
                    println!("{:?}", &expression);
                    println!("! {:?}", &reduction.to_de_bruijn(&HashMap::new()));
                    println!("! {:?}", &reduction);
                    panic!()
                }
            }
        }
    }
}
