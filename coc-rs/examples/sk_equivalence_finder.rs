use coc_rs::ic;
use coc_rs::introspective_calculus::{Formula, RWMFormula, RWMFormulaValue};
use std::collections::BTreeSet;

type Unfoldings<'a> = &'a [[Formula; 2]];
#[derive(Eq, PartialEq, Default, Debug)]
struct UnfoldingsUsed {
    indices: BTreeSet<usize>,
}

impl UnfoldingsUsed {
    fn extend_with(&mut self, other: &UnfoldingsUsed) {
        self.indices.extend(other.indices.iter().copied());
    }
}

fn unfold(f: RWMFormula, unfoldings: Unfoldings) -> (RWMFormula, UnfoldingsUsed) {
    for (index, [from, to]) in unfoldings.iter().enumerate() {
        if let Ok(substitutions) = from.to_rwm().substitutions_to_become(&f) {
            return (
                to.to_rwm().with_metavariables_replaced_rwm(&substitutions),
                UnfoldingsUsed {
                    indices: [index].into_iter().collect(),
                },
            );
        }
    }
    if let RWMFormulaValue::Apply(c) = f.value() {
        let [(a, mut ua), (b, ub)] = c.map(|c| unfold(c, unfoldings));
        ua.extend_with(&ub);
        return (Formula::apply([a.into(), b.into()]).to_rwm(), ua);
    }
    (f, UnfoldingsUsed::default())
}

fn unfold_lots(mut f: RWMFormula, unfoldings: Unfoldings) -> (RWMFormula, UnfoldingsUsed) {
    let mut result_unf = UnfoldingsUsed::default();
    for _ in 0..100 {
        let (next, unf) = unfold(f.clone(), unfoldings);
        if next == f {
            break;
        }
        result_unf.extend_with(&unf);
        f = next;
    }
    (f, result_unf)
}

#[derive(Eq, PartialEq)]
enum CheckResult {
    DidntFinish,
    IdenticalRebuild(UnfoldingsUsed),
    DistinctRebuild(RWMFormula),
}

impl CheckResult {
    fn print(&self) {
        match self {
            CheckResult::DidntFinish => {
                println!("Didn't finish")
            }
            CheckResult::IdenticalRebuild(u) => {
                println!("Identical rebuild using unfoldings {:?}", u)
            }
            CheckResult::DistinctRebuild(r) => {
                println!("Distinct rebuild, only got to {r}")
            }
        }
    }
}

fn check(f: RWMFormula, unfoldings: Unfoldings) -> CheckResult {
    let (result, _) = unfold_lots(ic!(((((f "A") "B") "C") "D") "E").to_rwm(), unfoldings);
    let (next, _) = unfold(result.clone(), unfoldings);
    if next != result {
        // println!("Didn't finish: {f}");
        return CheckResult::DidntFinish;
    }

    let rebuilt = ic!("A" => ("B" => ("C" => ("D" => ("E" => (result))))));
    let (ur, unf) = unfold_lots(rebuilt.to_rwm(), unfoldings);
    if ur != f {
        println!("{f} = {ur} = {rebuilt}");
        CheckResult::DistinctRebuild(ur)
    } else {
        CheckResult::IdenticalRebuild(unf)
    }
}

fn main() {
    let manual_tests = [
        ic!( "X" => ("Y" => (
            (
                fuse
                (
                    (fuse (const fuse))
                    ((fuse (const (fuse (const fuse)))) (fuse (const (fuse (const "X")))))
                )
            )
            (fuse (const (fuse (const "Y"))))
            ))
        ),
        ic!(((fuse ((fuse (const fuse)) (fuse (const (const "X"))))) (fuse id))),
        ic!(((fuse ((fuse (const fuse)) (const (const "X")))) (fuse id))),
    ];

    let basic_unfoldings = [
        [ic!((const "A") "B"), ic!("A")],
        [ic!(((fuse "A") "B") "C"), ic!(("A" "C") ("B" "C"))],
    ];
    let already_discovered_unfoldings = [
        [ic!((const "A") "B"), ic!("A")],
        [ic!(((fuse "A") "B") "C"), ic!(("A" "C") ("B" "C"))],
        [ic!(const ((fuse const) "A")), ic!(fuse const)], // "identity"
        [ic!(fuse (const (const "A"))), ic!(const (const "A"))],
        [ic!(fuse (fuse const)), ic!(id)], // i.e. "fuse (const id) = id"
        [
            ic!((fuse (const fuse)) (const (const "A"))),
            ic!(const (fuse (const "A"))),
        ], // i.e. "fuse (const id) = id"
        [
            ic!(((fuse ((fuse (const fuse)) (fuse (const "A")))) (fuse id))),
            ic!(fuse (fuse "A")),
        ],
        [
            ic!((fuse ((fuse (const fuse))(fuse (const "A")))) (fuse (const "B"))),
            ic!(fuse (const ((fuse "A") "B"))),
        ],
        [
            ic!("A"=>("B"=>("X"=>("Y"=>("Z"=>(("A" (("X" "Y") "Z")) ("B" (("X" "Y") "Z")))))))),
            ic!("A"=>("B"=>("X"=>("Y"=>("Z"=>((((fuse "A") "B") (("X" "Y") "Z")))))))),
        ],
    ];
    let unfoldings = &already_discovered_unfoldings;
    let already_discovered_redundant = [
        ic!(fuse(const(fuse const))), // instance of (fuse (const (const A)))
        ic!((fuse const) fuse),       // specialization of identity
        ic!((fuse const) "X"),        // specialization of identity
    ]
    .map(|f| f.to_rwm());

    for sides in already_discovered_unfoldings.clone() {
        println!("{} = {}", sides[0], sides[1]);
        let [a, b] = sides.map(|side| {
            unfold_lots(
                ic!(((((side "G") "H") "I") "J") "K").to_rwm(),
                &basic_unfoldings,
            )
            .0
        });
        assert_eq!(a, b);
    }
    for t in manual_tests {
        println!(
            "{}\n=\n{}\n=\n{}",
            t,
            unfold_lots(t.to_rwm(), unfoldings).0,
            unfold_lots(ic!(((((t "A") "B") "C") "D") "E").to_rwm(), unfoldings).0
        );
    }
    check(
        ic!(fuse (const (fuse (const ((fuse "X") "Y"))))).to_rwm(),
        unfoldings,
    )
    .print();
    check(ic!(fuse (const (fuse (const ("X"))))).to_rwm(), unfoldings).print();

    let mut formulas_by_size: Vec<Vec<RWMFormula>> = vec![
        vec![],
        vec![
            ic!(const).to_rwm(),
            ic!(fuse).to_rwm(),
            ic!("X").to_rwm(),
            // ic!("Y").to_rwm(),
        ],
    ];
    let mut num_found = 0;
    while formulas_by_size.len() <= 12 {
        let size_of_new_formulas = formulas_by_size.len();
        println!("Trying formulas of size {size_of_new_formulas}");
        let last = formulas_by_size.last().unwrap();
        // construct all non-unfoldable formulas of the new size
        let mut new_formulas: Vec<RWMFormula> = last
            .iter()
            .flat_map(|f| [ic!(const f).to_rwm(), ic!(fuse f).to_rwm()])
            .collect();
        for first_size in 1..=(size_of_new_formulas - 2) {
            let second_size = size_of_new_formulas - first_size - 1;
            assert_eq!(first_size + second_size + 1, size_of_new_formulas);
            for (ai, a) in formulas_by_size[first_size].iter().enumerate() {
                for (bi, b) in formulas_by_size[second_size].iter().enumerate() {
                    if (first_size != second_size) || (ai != bi) {
                        new_formulas.push(ic!((fuse a) b).to_rwm());
                    }
                }
            }
        }
        new_formulas.retain(|f| {
            unfold(f.clone(), unfoldings).0 == *f
                && already_discovered_redundant.iter().all(|r| r != f)
        });
        for f in &new_formulas {
            assert_eq!(f.naive_size(), size_of_new_formulas * 2 - 1, "{}", f);
            if matches!(
                check(f.clone(), unfoldings),
                CheckResult::DistinctRebuild(_)
            ) {
                num_found += 1;
                if num_found > 5 {
                    break;
                }
            }
        }
        formulas_by_size.push(new_formulas);
    }
}
