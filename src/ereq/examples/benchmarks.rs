use std::{
    collections::HashSet,
    fs::{self, read},
    io::BufRead,
    path::{Path, PathBuf},
    sync::mpsc,
    thread,
    time::Duration,
};

use ereq::{MSO, RegexBuilder};

fn base() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

struct MonaResults {
    sat: HashSet<String>,
    _unsat: HashSet<String>,
}

fn get_mona_results_prerecorded() -> MonaResults {
    let mona_sat = read(base().join("../../data/result-sat.txt"))
        .unwrap()
        .lines()
        .map(|v| v.unwrap())
        .collect::<HashSet<_>>();
    let mona_unsat = read(base().join("../../data/result-unsat.txt"))
        .unwrap()
        .lines()
        .map(|v| v.unwrap())
        .collect::<HashSet<_>>();
    MonaResults {
        sat: mona_sat,
        _unsat: mona_unsat,
    }
}

fn check_ereq_emptiness(input: String) -> (bool, u32) {
    const STACK_SIZE: usize = 1024 * 1024 * 1024;
    let (tx, rx) = mpsc::channel();
    thread::Builder::new()
        .name("solver".into())
        .stack_size(STACK_SIZE)
        .spawn(move || {
            let mut mso: MSO = MSO::new();
            let constraints = mso.parse_mona_m2l_str(&input).expect("failed to parse");
            let result = mso.b().is_empty_lang(constraints);
            let nodes = mso.b().node_count();
            mso.b().print_profile();
            tx.send((result, nodes))
        })
        .unwrap();
    rx.recv().unwrap()
}

fn run_file(expected: &MonaResults, file: &str, timeout_secs: u64) -> (u128, u32) {
    let resolved = base().join(file);
    let pbuf = PathBuf::from(file);
    let name = pbuf.file_name().unwrap().to_str().unwrap();
    let content = fs::read_to_string(&resolved).expect("failed to read input file");

    print!("{}.. ", file);
    let start = std::time::Instant::now();

    let (tx, rx) = mpsc::channel();
    let input = content.clone();
    thread::spawn(move || tx.send(check_ereq_emptiness(input)));

    let (is_empty, nodes) = match rx.recv_timeout(Duration::from_secs(timeout_secs)) {
        Ok(v) => v,
        Err(_) => panic!("timeout (>{}s): {}", timeout_secs, name),
    };

    let mona_sat = expected.sat.contains(name);
    assert_eq!(!is_empty, mona_sat, "mona different result: {}", file);

    let dur = std::time::Instant::now().duration_since(start);
    println!("{}ms, {} nodes", dur.as_millis(), nodes);
    (dur.as_millis(), nodes)
}

fn write_results(name: &str, results: &[(&str, u128, u32)], path: &str) {
    let mut md = String::new();
    md.push_str(&format!("# {} benchmark results\n\n", name));
    md.push_str(&format!(
        "## configuration\n\n```\n{}\n```\n\n",
        RegexBuilder::config_string()
    ));
    md.push_str("## results\n\n");
    md.push_str("| file | time (ms) | nodes |\n");
    md.push_str("|------|-----------|-------|\n");
    for (file, time_ms, nodes) in results {
        let fname = std::path::Path::new(file)
            .file_name()
            .unwrap()
            .to_str()
            .unwrap();
        md.push_str(&format!("| {} | {} | {} |\n", fname, time_ms, nodes));
    }
    let total_time: u128 = results.iter().map(|r| r.1).sum();
    let total_nodes: u64 = results.iter().map(|r| r.2 as u64).sum();
    md.push_str(&format!(
        "| **total** | **{}** | **{}** |\n",
        total_time, total_nodes
    ));
    let resolved = Path::new(path);
    fs::create_dir_all(resolved.parent().unwrap()).ok();
    fs::write(&resolved, md).expect("failed to write results");
    println!("wrote {}", resolved.display());
}

fn run_suite(name: &str, files: &[&str], output_path: &str, timeout_secs: u64) {
    let expected = get_mona_results_prerecorded();
    let mut results = Vec::new();

    for &file in files {
        let (time_ms, nodes) = run_file(&expected, file, timeout_secs);
        results.push((file, time_ms, nodes));
    }

    write_results(name, &results, output_path);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let filter = args.get(1).map(|s| s.as_str()).unwrap_or("all");

    if filter == "all" || filter == "lift" {
        println!("=== lift ===");
        run_suite(
            "lift",
            &[
                "../../data/lift/lift_2.ltl0.mona",
                "../../data/lift/lift_3.ltl0.mona",
                "../../data/lift/lift_4.ltl0.mona",
                "../../data/lift/lift_5.ltl0.mona",
                "../../data/lift/lift_6.ltl0.mona",
                "../../data/lift/lift_7.ltl0.mona",
                "../../data/lift/lift_8.ltl0.mona",
                "../../data/lift/lift_9.ltl0.mona",
            ],
            "results/benchmarks_lift.md",
            60,
        );
    }

    if filter == "all" || filter == "counter" {
        println!("=== counter ===");
        run_suite(
            "counter",
            &[
                "../../data/counter/counter_2.ltl0.mona",
                "../../data/counter/counter_3.ltl0.mona",
                "../../data/counter/counter_4.ltl0.mona",
                "../../data/counter/counter_5.ltl0.mona",
                "../../data/counter/counter_6.ltl0.mona",
                "../../data/counter/counter_7.ltl0.mona",
                "../../data/counter/counter_8.ltl0.mona",
                "../../data/counter/counter_9.ltl0.mona",
                "../../data/counter/counter_10.ltl0.mona",
                "../../data/counter/counter_11.ltl0.mona",
                "../../data/counter/counter_12.ltl0.mona",
                "../../data/counter/counter_13.ltl0.mona",
                "../../data/counter/counter_14.ltl0.mona",
                "../../data/counter/counter_15.ltl0.mona",
                "../../data/counter/counter_16.ltl0.mona",
            ],
            "results/benchmarks_counter.md",
            60,
        );
    }

    if filter == "all" || filter == "counter_l" {
        println!("=== counter_l ===");
        run_suite(
            "counter_l",
            &[
                "../../data/counter/counter_l_2.ltl0.mona",
                "../../data/counter/counter_l_3.ltl0.mona",
                "../../data/counter/counter_l_4.ltl0.mona",
                "../../data/counter/counter_l_5.ltl0.mona",
                "../../data/counter/counter_l_6.ltl0.mona",
                "../../data/counter/counter_l_7.ltl0.mona",
                "../../data/counter/counter_l_8.ltl0.mona",
                "../../data/counter/counter_l_9.ltl0.mona",
                "../../data/counter/counter_l_10.ltl0.mona",
                "../../data/counter/counter_l_11.ltl0.mona",
                "../../data/counter/counter_l_12.ltl0.mona",
                "../../data/counter/counter_l_13.ltl0.mona",
                "../../data/counter/counter_l_14.ltl0.mona",
                "../../data/counter/counter_l_15.ltl0.mona",
                "../../data/counter/counter_l_16.ltl0.mona",
            ],
            "results/benchmarks_counter_l.md",
            60,
        );
    }

    if filter == "all" || filter == "lift_b" {
        println!("=== lift_b ===");
        run_suite(
            "lift_b",
            &[
                "../../data/lift/lift_b_2.ltl0.mona",
                "../../data/lift/lift_b_3.ltl0.mona",
                "../../data/lift/lift_b_4.ltl0.mona",
                "../../data/lift/lift_b_5.ltl0.mona",
                "../../data/lift/lift_b_6.ltl0.mona",
                "../../data/lift/lift_b_7.ltl0.mona",
                "../../data/lift/lift_b_8.ltl0.mona",
                "../../data/lift/lift_b_9.ltl0.mona",
            ],
            "results/benchmarks_lift_b.md",
            60,
        );
    }

    if filter == "all" || filter == "szymanski" {
        println!("=== szymanski ===");
        run_suite(
            "szymanski",
            &[
                "../../data/szymanski/zn.ltl0.mona",
                "../../data/szymanski/zp1.ltl0.mona",
                "../../data/szymanski/zp2.ltl0.mona",
                "../../data/szymanski/zp3.ltl0.mona",
            ],
            "results/benchmarks_szymanski.md",
            60,
        );
    }
}
