#![feature(default_free_fn)]

use std::collections::HashMap;
use std::default::default;
use std::rc::Rc;
use coc_rs::term::{PROP, TermArrayVec, TermEnvironment, RecursiveTermKind, TYPE, FormatTermOptions};

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
struct TermExtremity {
    height: usize,
    max_index_overflow: u64,
}

#[derive(Default)]
struct TermGenerator {
    terms: HashMap<TermExtremity, Rc<Vec<TermArrayVec>>>,
    environment: TermEnvironment,
}

impl TermGenerator {
    fn all_of_extremity(&mut self, extremity: TermExtremity) -> Rc<Vec<TermArrayVec>> {
        if let Some(result) = self.terms.get(&extremity) {
            return result.clone();
        }
        let mut result = Vec::new();
        if extremity.height == 0 {
            if extremity.max_index_overflow == 0 {
                result = vec![PROP.to_term_array_vec(), TYPE.to_term_array_vec()]
            } else {
                result = vec![TermArrayVec::variable(extremity.max_index_overflow - 1)]
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
                                if (i1 == needed_overflow_1 || i2 == needed_overflow_2 || extremity.max_index_overflow == 0)
                                    && (h1 == needed_height || h2 == needed_height) {
                                    let e1 = TermExtremity { height: h1, max_index_overflow: i1 };
                                    let e2 = TermExtremity { height: h2, max_index_overflow: i2 };
                                    let ts1 = self.all_of_extremity(e1);
                                    let ts2 = self.all_of_extremity(e2);
                                    for t1 in &*ts1 {
                                        for t2 in &*ts2 {
                                            result.push(self.environment.make_recursive_term(kind, [t1.as_term_ref(), t2.as_term_ref()]));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        self.terms.entry(extremity).or_insert_with(|| Rc::new(result)).clone()
    }
}

fn main() {
    // enumerate all terms lol
    let mut generator = TermGenerator::default();
    for height in 0..3 {
        for term in &*generator.all_of_extremity(TermExtremity { height, max_index_overflow: 0 }) {
            let term = generator.environment.display_term(FormatTermOptions { depth: 5, ..default() }, term.as_term_ref());
            println!("{}", term);
        }
    }
}