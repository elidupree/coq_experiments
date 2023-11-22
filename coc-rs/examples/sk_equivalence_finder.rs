use coc_rs::ic;
use coc_rs::introspective_calculus::{Formula, RWMFormula, RWMFormulaValue};

type Unfoldings<'a> = &'a [[Formula; 2]];

fn unfold(f: RWMFormula, unfoldings: Unfoldings) -> RWMFormula {
    for [from, to] in unfoldings {
        if let Ok(substitutions) = from.to_rwm().substitutions_to_become(&f) {
            return to.to_rwm().with_metavariables_replaced_rwm(&substitutions);
        }
    }
    if let RWMFormulaValue::Apply(c) = f.value() {
        return Formula::apply(c.map(|c| unfold(c, unfoldings).into())).to_rwm();
    }
    f
}

fn unfold_lots(mut f: RWMFormula, unfoldings: Unfoldings) -> RWMFormula {
    for _ in 0..100 {
        let next = unfold(f.clone(), unfoldings);
        if next == f {
            return f;
        }
        f = next;
    }
    f
}

// enum CheckResult {}

fn check(f: RWMFormula, unfoldings: Unfoldings) -> bool {
    let result = unfold_lots(ic!(((((f "A") "B") "C") "D") "E").to_rwm(), unfoldings);
    let next = unfold(result.clone(), unfoldings);
    if next != result {
        // println!("Didn't finish: {f}");
        return false;
    }

    let rebuilt = ic!("A" => ("B" => ("C" => ("D" => ("E" => (result))))));
    let ur = unfold_lots(rebuilt.to_rwm(), unfoldings);
    if ur != f {
        println!("{f} = {ur} = {rebuilt}");
        true
    } else {
        false
    }
}

fn main() {
    let manual_tests = [
        ic!(
            (
                fuse
                (
                    (fuse (const fuse))
                    ((fuse (const (fuse (const fuse)))) (fuse (const (fuse (const "X")))))
                )
            )
            (fuse (const (fuse (const "Y"))))
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
        });
        assert_eq!(a, b);
    }
    for t in manual_tests {
        println!(
            "{}\n=\n{}\n=\n{}",
            t,
            unfold_lots(t.to_rwm(), unfoldings),
            unfold_lots(ic!(((((t "A") "B") "C") "D") "E").to_rwm(), unfoldings)
        );
    }
    dbg!(check(
        ic!(fuse (const (fuse (const ((fuse "X") "Y"))))).to_rwm(),
        unfoldings,
    ));
    dbg!(check(
        ic!(fuse (const (fuse (const ("X"))))).to_rwm(),
        unfoldings
    ));

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
            unfold(f.clone(), unfoldings) == *f
                && already_discovered_redundant.iter().all(|r| r != f)
        });
        for f in &new_formulas {
            assert_eq!(f.naive_size(), size_of_new_formulas * 2 - 1, "{}", f);
            if check(f.clone(), unfoldings) {
                num_found += 1;
                if num_found > 5 {
                    break;
                }
            }
        }
        formulas_by_size.push(new_formulas);
    }
}
