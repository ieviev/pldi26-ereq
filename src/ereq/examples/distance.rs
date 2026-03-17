// distance benchmark
//
// tests the distance formula family where the DFA state space grows
// exponentially with parameter n.
//
// usage:
//   cargo run --release --features low_cost_simplify,low_high_limit --example distance -p ereq -- [max_n]

use std::{env, fs, path::Path, sync::mpsc, thread, time::Duration};

use ereq::{MSO, RegexBuilder};

fn distance_formula(n: usize) -> String {
    format!(
        "
m2l-str;
var2 A;
(all1 x0: (x0 in A) <=> (ex1 x1: x1 = x0 + 1 & (x1 notin A)));
(0 in A);
(ex1 x0: (x0 in A) & (ex1 x1: (x1 = x0 + {n}) & (x1 notin A)));
        "
    )
}

struct Result {
    n: usize,
    is_empty: bool,
    nodes: u32,
    time_ms: u128,
}

fn write_results(max_n: usize, results: &[Result]) {
    let mut md = String::new();
    md.push_str("# distance benchmark results\n\n");
    md.push_str(&format!(
        "## configuration\n\n```\n{}\n```\n\n",
        RegexBuilder::config_string()
    ));
    md.push_str(&format!("n=2..{max_n}\n\n"));
    md.push_str("## results\n\n");
    md.push_str("| n | result | nodes | time (ms) |\n");
    md.push_str("|---|--------|-------|-----------|\n");
    for r in results {
        let result_str = if r.is_empty { "unsat" } else { "sat" };
        md.push_str(&format!(
            "| {} | {} | {} | {} |\n",
            r.n, result_str, r.nodes, r.time_ms
        ));
    }
    let total_time: u128 = results.iter().map(|r| r.time_ms).sum();
    let total_nodes: u64 = results.iter().map(|r| r.nodes as u64).sum();
    md.push_str(&format!(
        "| **total** | | **{}** | **{}** |\n",
        total_nodes, total_time
    ));

    let path = Path::new("results/benchmarks_distance.md");
    fs::create_dir_all(path.parent().unwrap()).ok();
    fs::write(path, md).expect("failed to write results");
    println!("\nwrote {}", path.display());
}

fn main() {
    let max_n: usize = env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(20);

    println!("distance benchmark: n=2..{max_n}");
    println!("config: {}\n", RegexBuilder::config_string());
    println!(
        "{:<4} {:<8} {:<12} {:<10}",
        "n", "result", "nodes", "time (ms)"
    );
    println!("{}", "-".repeat(38));

    let mut results = Vec::new();

    for n in 2..=max_n {
        let formula = distance_formula(n);
        let (tx, rx) = mpsc::channel();
        const STACK_SIZE: usize = 4 * 1024 * 1024 * 1024;
        thread::Builder::new()
            .name("solver".into())
            .stack_size(STACK_SIZE)
            .spawn(move || {
                let start = std::time::Instant::now();
                let mut mso: MSO = MSO::new();
                let constraints = mso.parse_mona_m2l_str(&formula).expect("failed to parse");
                let result = mso.b().is_empty_lang(constraints);
                let elapsed = start.elapsed();
                let nodes = mso.b().node_count();
                mso.b().print_profile();
                tx.send((result, nodes, elapsed)).ok();
            })
            .unwrap();

        match rx.recv_timeout(Duration::from_secs(120)) {
            Ok((is_empty, nodes, elapsed)) => {
                let time_ms = elapsed.as_millis();
                let result_str = if is_empty { "unsat" } else { "sat" };
                println!("{:<4} {:<8} {:<12} {:<10}", n, result_str, nodes, time_ms);
                results.push(Result {
                    n,
                    is_empty,
                    nodes,
                    time_ms,
                });
            }
            Err(_) => {
                println!("{:<4} TIMEOUT (120s)", n);
                break;
            }
        }
    }

    write_results(max_n, &results);
}
