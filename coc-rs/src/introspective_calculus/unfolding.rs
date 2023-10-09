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
    pub fn unfold_left(&mut self, levels_deduction_available_under: u32) -> bool {
        if self.unfold_here() {
            return true;
        }
        match_ic!(self, {
            ((implies l) r) => {
                if let Some(less) = levels_deduction_available_under.checked_sub(1) {
                    let mut l = l.clone();
                    let mut r = r.clone();
                    if l.unfold_left(less) || r.unfold_left(less) {
                        *self = ic!((implies l) r);
                        return true
                    }
                }
            },
            ((union l) r) => {
                let mut l = l.clone();
                let mut r = r.clone();
                if l.unfold_left(levels_deduction_available_under) || r.unfold_left(levels_deduction_available_under) {
                    *self = ic!((union l) r);
                    return true
                }
            },
            (all r) => {
                let mut r = r.clone();
                if r.unfold_left(levels_deduction_available_under) {
                    *self = ic!(all r);
                    return true
                }
            },
            (l r) => {
                let mut l = l.clone();
                if l.unfold_left(levels_deduction_available_under) {
                    *self = ic!(l r.clone());
                    return true
                }
            },
        });
        false
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
