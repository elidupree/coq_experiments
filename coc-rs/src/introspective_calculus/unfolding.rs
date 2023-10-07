use crate::ic;
use crate::introspective_calculus::{Atom, Formula};
use std::sync::Arc;

impl Formula {
    pub fn unfold_here(&mut self) -> bool {
        if let Formula::Apply(a1) = self {
            let [s2, last] = &**a1;
            if let Formula::Apply(a2) = s2 {
                if a2[0] == Formula::Atom(Atom::Const) {
                    *self = a2[1].clone();
                    return true;
                } else if let Formula::Apply(a3) = &a2[0] {
                    if a3[0] == Formula::Atom(Atom::Fuse) {
                        let a = a3[1].clone();
                        let b = a2[1].clone();
                        let c = last.clone();
                        *self = ic!((a c.clone())(b c));
                        return true;
                    }
                }
            }
        }
        false
    }
    pub fn unfold_left(&mut self) -> bool {
        self.unfold_here()
            || match self {
                Formula::Apply(c) => {
                    let mut l = c[0].clone();
                    if l.unfold_left() {
                        let r = c[1].clone();
                        *self = Formula::Apply(Arc::new([l, r]));
                        true
                    } else {
                        false
                    }
                }
                _ => false,
            }
    }
    pub fn unfold_many(&mut self) -> usize {
        // self.children_mut()
        //     .into_iter()
        //     .map(|c| c.unfold_many())
        //     .sum::<usize>()
        //     + self.unfold_here() as usize
        let mut result = self.unfold_here() as usize;
        *self = self.map_children(|c| {
            let mut c = c.clone();
            result += c.unfold_many();
            c
        });
        result
    }
    pub fn unfold_until(&mut self, max: usize) {
        let mut total = 0;
        loop {
            let n = self.unfold_many();
            total += n;
            if n == 0 || total > max {
                return;
            }
        }
    }
}
