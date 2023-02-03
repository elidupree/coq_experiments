#![feature(default_free_fn)]

use coc_rs::term::{RecursiveTermKind, Term};
use coc_rs::types::{is_fully_reduced, naive_fully_reduce, naive_type_check, TypeCheckResult};
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
struct TermExtremity {
    height: usize,
    max_index_overflow: u64,
}

#[derive(Default)]
struct TermGenerator {
    terms: HashMap<TermExtremity, Rc<Vec<(Term, Option<Term>)>>>,
}

impl TermGenerator {
    fn all_of_extremity(&mut self, extremity: TermExtremity) -> Rc<Vec<(Term, Option<Term>)>> {
        if let Some(result) = self.terms.get(&extremity) {
            return result.clone();
        }
        let mut result = Vec::new();
        if extremity.height == 0 {
            if extremity.max_index_overflow == 0 {
                result = vec![(Term::prop(), Some(Term::t())), (Term::t(), None)]
            } else {
                result = vec![(Term::variable(extremity.max_index_overflow - 1), None)]
            }
        } else {
            use RecursiveTermKind::*;
            for (kind, offset) in [(Lambda, 1), (ForAll, 1), (Apply, 0)] {
                let needed_overflow_1 = extremity.max_index_overflow;
                let needed_overflow_2 = extremity.max_index_overflow + offset;
                let needed_height = extremity.height - 1;
                for h1 in 0..=needed_height {
                    for h2 in 0..=needed_height {
                        for i1 in 0..=needed_overflow_1 {
                            for i2 in 0..=needed_overflow_2 {
                                if (i1 == needed_overflow_1
                                    || i2 == needed_overflow_2
                                    || extremity.max_index_overflow == 0)
                                    && (h1 == needed_height || h2 == needed_height)
                                {
                                    let e1 = TermExtremity {
                                        height: h1,
                                        max_index_overflow: i1,
                                    };
                                    let e2 = TermExtremity {
                                        height: h2,
                                        max_index_overflow: i2,
                                    };
                                    let ts1 = self.all_of_extremity(e1);
                                    let ts2 = self.all_of_extremity(e2);
                                    for (t1, _) in &*ts1 {
                                        for (t2, _) in &*ts2 {
                                            let term = Term::recursive(
                                                kind,
                                                [t1.as_term_ref(), t2.as_term_ref()],
                                            );
                                            if is_fully_reduced(term.as_term_ref()) {
                                                let ty = naive_type_check(term.as_term_ref(), &[]);
                                                match ty {
                                                    Some(TypeCheckResult::HasType(ty)) => {
                                                        result.push((term, Some(ty)))
                                                    }
                                                    None => result.push((term, None)),
                                                    Some(TypeCheckResult::NoType) => {}
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        self.terms
            .entry(extremity)
            .or_insert_with(|| Rc::new(result))
            .clone()
    }
}

fn main() {
    // enumerate all terms lol
    let mut generator = TermGenerator::default();
    for height in 0..4 {
        for (term, ty) in &*generator.all_of_extremity(TermExtremity {
            height,
            max_index_overflow: 0,
        }) {
            print!("{}", term);
            if let Some(ty) = ty {
                print!(" : {}", ty);
            }
            println!();
            let reduced = naive_fully_reduce(term.as_term_ref());
            if &reduced != term {
                println!("->β {}", reduced);
            }
        }
    }
}
