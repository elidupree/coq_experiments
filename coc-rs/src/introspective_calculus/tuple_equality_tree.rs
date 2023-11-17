use crate::introspective_calculus::inference::ProvenInference;
use crate::introspective_calculus::{Formula, FormulaTrait, FormulaValue, RWMFormula, ToFormula};
use crate::{ic, substitutions};
use std::collections::BTreeMap;
use std::iter::zip;

#[derive(Clone)]
pub enum TupleEqualityTree<F> {
    Element([F; 2]),
    Tuple(Vec<TupleEqualityTree<F>>),
}

impl<F: FormulaTrait> TupleEqualityTree<F> {
    pub fn sides(&self) -> [F; 2] {
        match self {
            TupleEqualityTree::Element(sides) => sides.each_ref().map(F::clone),
            TupleEqualityTree::Tuple(children) => {
                let (a, b) = children
                    .iter()
                    .map(|c| {
                        let [a, b] = c.sides();
                        (a.into(), b.into())
                    })
                    .unzip();
                [
                    Formula::tuple(a).try_into().ok().unwrap(),
                    Formula::tuple(b).try_into().ok().unwrap(),
                ]
            }
        }
    }
    pub fn formula(&self) -> F {
        let [a, b] = self.sides();
        ic!(a = b).try_into().ok().unwrap()
    }
    pub fn to_rwm(&self) -> TupleEqualityTree<RWMFormula> {
        match self {
            TupleEqualityTree::Element(sides) => {
                TupleEqualityTree::Element(sides.each_ref().map(|side| side.into()))
            }
            TupleEqualityTree::Tuple(children) => {
                TupleEqualityTree::Tuple(children.iter().map(|c| c.to_rwm()).collect())
            }
        }
    }

    pub fn unpack_all(
        &self,
        self_side_representation: Option<Formula>,
        mut context: BTreeMap<String, [F; 2]>,
        continuation: impl FnOnce(BTreeMap<String, [F; 2]>) -> Option<Formula>,
    ) -> Option<Formula> {
        match self {
            TupleEqualityTree::Element(sides) => {
                assert!(
                    !context.is_empty(),
                    "we don't currently support unpacking singletons by themselves"
                );
                // now self_side_representation is already a variable containing this,
                let FormulaValue::Metavariable(name) = self_side_representation.unwrap().value()
                else {
                    panic!()
                };
                assert_eq!(context.get(name), Some(sides));
                // so we don't need to capture anything
                continuation(context)
            }
            TupleEqualityTree::Tuple(children) => {
                let names: Vec<String> = children.iter().map().collect();
                for (name, child) in zip(&names, children) {
                    context.insert(name.clone(), child.sides());
                }
                let mut continuation: Box<dyn FnOnce(BTreeMap<String, [F; 2]>) -> Option<Formula>> =
                    Box::new(continuation);
                for (name, child) in zip(&names, children).rev() {
                    let var = name.to_formula();
                    continuation =
                        Box::new(move |context| child.unpack_all(Some(var), context, continuation))
                }

                let mut result = continuation(context)?;

                // let name = format!("TETExtPlaceholder{}", vars.len());
                // let mut result = continuation;
                for name in names.into_iter().rev() {
                    result = ic!(name => result)
                }
                if let Some(self_side_representation) = self_side_representation {
                    result = ic!(self_side_representation result)
                }
                Some(result)
            }
        }
    }

    fn extraction_helper(&self, providers: &BTreeMap<[F; 2], String>) -> Option<Formula> {
        match self {
            TupleEqualityTree::Element(sides) => providers.get(sides).map(|s| s.to_formula()),
            TupleEqualityTree::Tuple(children) => children
                .iter()
                .map(|child| child.extraction_helper(providers))
                .collect::<Option<Vec<Formula>>>()
                .map(Formula::tuple),
        }
    }

    pub fn extractor(&self, other: &TupleEqualityTree<F>) -> Option<Formula> {
        self.unpack_all(None, BTreeMap::new(), |bindings| {
            let providers: BTreeMap<[F; 2], String> = bindings
                .into_iter()
                .map(|(name, value)| (value, name))
                .collect();
            other.extraction_helper(&providers)
        })
    }

    /// return self |- other
    pub fn external_extraction(&self, other: &TupleEqualityTree<F>) -> Option<ProvenInference> {
        let extractor = self.extractor(other)?;
        let a = self.sides();
        let [c0, c1] = other.sides();
        let b = a.map(|s| ic!(s extractor));
        let b_eq_c = [
            ProvenInference::fold_equivalence(c0.into(), b[0].to_rwm())?,
            ProvenInference::fold_equivalence(b[1].to_rwm(), c1.into())?,
        ];
        let a_to_b = ProvenInference::compatibility_left()
            .specialize(&substitutions! {"A":=a[0],"B":=a[1], "C":=extractor});
        // then use eq_trans on b_eq_c halves
    }

    /// return |- ((self,) = (self, other))
    pub fn internal_extraction(&self, other: &TupleEqualityTree<F>) -> Option<ProvenInference> {
        let extractor = self.extractor(other)?;
        let self_sides = self.sides();
        let other_sides = other.sides();
        let a = self.formula();
        let a_sides = self_sides.map(|s| ic!((s,)));
        let b_sides = self_sides.map(|s| ic!((s, (s extractor))));
        let a = ic!({ a_sides[0] } = { a_sides[1] }).to_rwm();
        let b = ic!({ b_sides[0] } = { b_sides[1] }).to_rwm();
        let c =
            ic!(({ self_sides[0] }, { other_sides[0] }) = ({ self_sides[1] }, { other_sides[1] }))
                .to_rwm();
        let b_eq_c = ProvenInference::fold_equivalence(b, c)?;
        // derive a=b by internal specialization
        // and then trans it with b_eq_c to get a=c
    }

    pub fn equivalence(&self, other: &TupleEqualityTree<F>) -> Option<ProvenInference> {
        let a = self.internal_extraction(other)?;
        let b = other.internal_extraction(self)?;
        Some(
            ProvenInference::derive_chain(
                "mutual_implication_gives_equality",
                vec![a, b],
                &ic!({ self.formula() } = { other.formula() }).to_rwm(),
            )
            .unwrap(),
        )
    }

    pub fn extend_with_conclusion(
        &self,
        proof: ProvenInference,
    ) -> Option<(TupleEqualityTree<F>, ProvenInference)> {
        let [p, pc] = proof.conclusion.as_eq_sides().unwrap();
        let TupleEqualityTree::Tuple([.., c]) = p else {
            return None;
        };
        let TupleEqualityTree::Tuple(mut children_with_c) = self.clone() else {
            return None;
        };
        children_with_c.push(c);
        let with_p = TupleEqualityTree::Tuple(vec![self.clone(), p]);
        let with_pc = TupleEqualityTree::Tuple(vec![self.clone(), pc]);
        let with_c = TupleEqualityTree::Tuple(children_with_c);
        let e1 = self.equivalence(&with_p)?;
        let e2 = ProvenInference::derive_chain(
            "substitute_in_conjunction_right",
            vec![proof.clone()],
            &ic!(with_p = with_pc).to_rwm(),
        )
        .unwrap();
        let e3 = with_pc.equivalence(&with_c)?;
        Some((
            with_c,
            ProvenInference::eq_trans_chain(&[e1, e2, e3]).unwrap(),
        ))
    }
}
