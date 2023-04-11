use crate::introspective_calculus::{Atom, Formula};
use std::mem;

impl Formula {
    pub fn unfold_here(&mut self) -> bool {
        if let Formula::Apply(a1) = self {
            let [s2, last] = &mut **a1;
            if let Formula::Apply(a2) = s2 {
                if a2[0] == Formula::Atom(Atom::Const) {
                    *self = mem::take(&mut a2[1]);
                    return true;
                } else if let Formula::Apply(a3) = &mut a2[0] {
                    if a3[0] == Formula::Atom(Atom::Fuse) {
                        let a = mem::take(&mut a3[1]);
                        let b = mem::take(&mut a2[1]);
                        let c = mem::take(last);
                        a2[0] = a;
                        a2[1] = c.clone();
                        *last = Formula::Apply(Box::new([b, c]));
                        return true;
                    }
                }
            }
        }
        false
    }
    pub fn unfold_many(&mut self) -> usize {
        self.children_mut()
            .into_iter()
            .map(|c| c.unfold_many())
            .sum::<usize>()
            + self.unfold_here() as usize
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
