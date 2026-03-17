// demonstrates that MONA considers forall on the empty string unsatisfiable.
//
// in M2L-STR semantics, strings must be nonempty. we enforce this by intersecting
// with (_+) after formula translation. without this intersection, formulas that
// are only satisfiable on the empty string (via vacuous forall) get wrong results.
//
// usage:
//   cargo run --example forall_empty_string -p tests

use ereq::MSO;

struct Case {
    name: &'static str,
    formula: &'static str,
}

const CASES: &[Case] = &[
    // x < x is false for every position, but vacuously true on empty string
    Case {
        name: "all1 x: x < x",
        formula: "m2l-str; all1 x: x < x;",
    },
    // "no position exists" - only true on empty string
    Case {
        name: "~(ex1 x: 0 <= x)",
        formula: "m2l-str; ~(ex1 x: 0 <= x);",
    },
    // conjunction of contradictions, still vacuously true on empty string
    Case {
        name: "all1 x: x < x & x < x",
        formula: "m2l-str; all1 x: (x < x & x < x);",
    },
    // x in A & x notin A is a contradiction, vacuously true on empty string
    Case {
        name: "var2 A; all1 x: x in A & x notin A",
        formula: "m2l-str; var2 A; all1 x: x in A & x notin A;",
    },
];

fn run(formula: &str, with_tp: bool) -> bool {
    let mut mso = MSO::new();
    let constraints = if with_tp {
        mso.parse_mona_m2l_str(formula)
    } else {
        mso.parse_m2l_str_wo_mona(formula)
    }
    .expect("parse failed");
    let is_empty = mso.b().is_empty_lang(constraints);
    !is_empty // return satisfiability
}

fn main() {
    println!("MONA forall on empty string experiment");
    println!("=======================================\n");
    println!(
        "MONA's M2L-STR requires nonempty strings. we intersect with (_+) to match.\n\
         without (_+), the empty string can vacuously satisfy forall, giving wrong results.\n"
    );

    println!(
        "{:<45} {:>15} {:>15}",
        "formula", "with (_+)", "without (_+)"
    );
    println!("{}", "-".repeat(77));

    let mut all_match = true;
    for case in CASES {
        let with_tp = run(case.formula, true);
        let without_tp = run(case.formula, false);
        let differs = with_tp != without_tp;
        if differs {
            all_match = false;
        }

        println!(
            "{:<45} {:>15} {:>15}{}",
            case.name,
            if with_tp { "SAT" } else { "UNSAT" },
            if without_tp { "SAT" } else { "UNSAT" },
            if differs { "  <-- differs!" } else { "" }
        );
    }

    println!("\n{}", "-".repeat(77));
    if !all_match {
        println!(
            "formulas where results differ demonstrate the effect of the (_+) intersection.\n\
             MONA says UNSAT for all of these because the empty string is excluded.\n\
             without (_+), the empty string vacuously satisfies forall, so we get SAT."
        );
    }
}
