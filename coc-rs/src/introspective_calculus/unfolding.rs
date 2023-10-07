use crate::introspective_calculus::{Atom, Formula};
use crate::{ic, match_ic};
use std::sync::Arc;

impl Formula {
    pub fn unfold_here(&mut self) -> bool {
        match_ic!(self, {
            ((const a) _b) => {*self = a.clone(); true },
            (((fuse a) b) c) => {*self = ic!(((a.clone()) c.clone())((b.clone()) c.clone())); true },
            _ => false,
        })
    }
    pub fn unfold_left(&mut self) -> bool {
        self.unfold_here()
            || match_ic!(self, {
                (l r) => {
                    let mut l = l.clone();
                    if l.unfold_left() {
                        *self = ic!(l r.clone());
                        true
                    } else {
                        false
                    }
                },
                _ => false,
            })
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
