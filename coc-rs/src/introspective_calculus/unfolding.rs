use crate::introspective_calculus::Formula;
use crate::{ic, match_ic};

impl Formula {
    pub fn unfold_here(&mut self) -> bool {
        match_ic!(self, {
            ((const a) _b) => {*self = a.clone(); true },
            (((fuse a) b) c) => {*self = ic!((a c)(b c)); true },
            _ => false,
        })
    }
    // pub fn unfold_left(&mut self, levels_deduction_available_under: u32) -> bool {
    //     if self.unfold_here() {
    //         return true;
    //     }
    //     match_ic!(self, {
    //         ((implies l) r) => {
    //             if let Some(less) = levels_deduction_available_under.checked_sub(1) {
    //                 let mut l = l.clone();
    //                 let mut r = r.clone();
    //                 if l.unfold_left(less) || r.unfold_left(less) {
    //                     *self = ic!((implies l) r);
    //                     return true
    //                 }
    //             }
    //         },
    //         ((and l) r) => {
    //             let mut l = l.clone();
    //             let mut r = r.clone();
    //             if l.unfold_left(levels_deduction_available_under) || r.unfold_left(levels_deduction_available_under) {
    //                 *self = ic!((and l) r);
    //                 return true
    //             }
    //         },
    //         (all r) => {
    //             let mut r = r.clone();
    //             if r.unfold_left(levels_deduction_available_under) {
    //                 *self = ic!(all r);
    //                 return true
    //             }
    //         },
    //         (l r) => {
    //             let mut l = l.clone();
    //             if l.unfold_left(levels_deduction_available_under) {
    //                 *self = ic!(l r.clone());
    //                 return true
    //             }
    //         },
    //     });
    //     false
    // }
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

    // pub fn fancy_unfold_here(&self) -> Option<TrueFormula> {
    //     match_ic!(self, {
    //         ((const a) b) => {Some(TrueFormula::definition_of_const(a.clone(), b.clone())) },
    //         (((fuse a) b) c) => {Some(TrueFormula::definition_of_fuse(a.clone(),b.clone(), c.clone())) },
    //         ((name => body) argument) => Some(fancy_unfold_lambda(name, body, argument, self)),
    //         _ => None,
    //     })
    // }
}

// /// assumes `body` is a pretty formula with `Metavariable`s for variable_name, not combinators
// /// raw_form is of (variable_name => body)
// /// returns (raw_form argument) = body[variable_name:=argument]
// fn (fancy_unfold_lambda
//     variable_name: &str,
//     body: &Formula,
//     argument: &Formula,
//     raw_form: &Formula,
// ) -> Option<TrueFormula> {
//     match &body.value {
//         FormulaValue::Atom(_) => {}
//         FormulaValue::Apply(children) => {
//             let raw_children = match_ic!(raw_form, {
//                 ((fuse l) r) => [l, r],
//                 _ => return None,
//             });
//             let unfoldings = children
//                 .iter()
//                 .zip(raw_children)
//                 .map(|(c, r)| fancy_unfold_lambda(variable_name, c, argument, r))
//                 .collect::<Option<[TrueFormula; 2]>>()?;
//             let new_forms = unfoldings.map(|u| u.as_eq_sides().unwrap()[1]);
//
//             let c1_raw_form_arg_equals_fused = TrueFormula::definition_of_fuse(raw_children[0].clone(), raw_children[1].clone(), argument.clone());
//             let acbc_equals_ebc = TrueFormula::compatibility_left(&unfoldings[0], ic!({raw_children[1]} argument));
//             let acbc_equals_ebc = TrueFormula::compatibility_left(&unfoldings[0], ic!({raw_children[1]} argument));
//             let c2_c1_equals_
//         }
//         FormulaValue::And(_) => {}
//         FormulaValue::Equals(_) => {}
//         FormulaValue::Implies(_) => {}
//         FormulaValue::NamedGlobal { .. } => {}
//         FormulaValue::Metavariable(v2) => {
//             assert_eq!(v2, variable_name, "shouldn't reach this case");
//         }
//         FormulaValue::NameAbstraction(_, _, _) => {}
//     }
//     match_ic!(body, {
//         {
//             Formula::metavariable(variable_name.to_string())
//         }
//     })
// }
