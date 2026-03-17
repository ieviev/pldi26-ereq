// gaston horn clause benchmarks - comparison only
//
// these benchmarks come from the Gaston WS1S decision procedure
// (https://github.com/tfiedor/gaston, TACAS'17).
// they use WS1S semantics, not M2L-STR. our solver uses M2L-STR,
// so results are NOT expected to match. this is included only for
// performance comparison on shared MONA syntax, not correctness.
//
// only the horn_leq suites are included (92 files). the remaining
// 6 suites (horn_in, horn_trans, set_closed, set_obvious,
// set_singletons, strand) use MONA features not in our parser:
// comma-separated quantifier variables and pred definitions.

use std::{
    fs::{self, read_dir},
    io::Read as _,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::mpsc,
    thread,
    time::Duration,
};

use ereq::{MSO, RegexBuilder};
use wait_timeout::ChildExt;

fn base() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn gaston_dir() -> PathBuf {
    base().join("../../data/gaston")
}

const SUITES: &[&str] = &[
    // supported: nested existential/universal quantifiers with <, &, ~
    "horn_leq_0alt",
    "horn_leq_1alt",
    "horn_leq_2alt",
    "horn_leq_3alt",
    "horn_leq_4alt",
    // unsupported: use MONA features not in our parser
    // (comma-separated quantifier variables, pred definitions, set ops)
    // "horn_in",        // all1 x1, x2: ...
    // "horn_trans",     // all1 x1, x2: ...
    // "set_closed",     // pred definitions, set membership chains
    // "set_obvious",    // pred definitions
    // "set_singletons", // pred definitions
    // "strand",         // pred definitions (close, before, validmodel, ...)
];

const SKIP_FILES: &[&str] = &[];

fn get_suite_files(suite: &str) -> Vec<PathBuf> {
    let dir = gaston_dir().join(suite);
    let mut files: Vec<PathBuf> = read_dir(&dir)
        .unwrap_or_else(|e| panic!("failed to read {}: {}", dir.display(), e))
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| {
            p.extension().is_some_and(|e| e == "mona")
                && !SKIP_FILES.iter().any(|s| p.file_name().unwrap() == *s)
        })
        .collect();
    files.sort();
    files
}

struct BenchResult {
    file: String,
    suite: String,
    time_ms: u128,
    nodes: u32,
    is_empty: bool,
    status: &'static str, // "ok", "timeout", "crash"
}

fn run_single(file: &str) {
    let content = fs::read_to_string(file).expect("failed to read input file");
    const STACK_SIZE: usize = 1024 * 1024 * 1024;
    let (tx, rx) = mpsc::channel();
    thread::Builder::new()
        .name("solver".into())
        .stack_size(STACK_SIZE)
        .spawn(move || {
            let mut mso = MSO::new();
            let constraints = mso.parse_mona_m2l_str(&content).expect("failed to parse");
            let result = mso.b().is_empty_lang(constraints);
            let nodes = mso.b().node_count();
            mso.b().print_profile();
            tx.send((result, nodes)).ok();
        })
        .unwrap();
    let (is_empty, nodes) = rx.recv().unwrap();
    println!("RESULT {} {}", is_empty, nodes);
}

fn run_file_subprocess(suite: &str, file: &Path, timeout_secs: u64) -> BenchResult {
    let name = file.file_name().unwrap().to_str().unwrap().to_string();
    let start = std::time::Instant::now();
    let exe = std::env::current_exe().unwrap();
    let child = Command::new(&exe)
        .args(["--run-single", file.to_str().unwrap()])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn();

    let mut child = match child {
        Ok(c) => c,
        Err(e) => {
            println!("{}: spawn error: {}", name, e);
            return BenchResult { file: name, suite: suite.into(), time_ms: 0, nodes: 0, is_empty: false, status: "crash" };
        }
    };

    let timeout = Duration::from_secs(timeout_secs);
    match child.wait_timeout(timeout) {
        Ok(Some(status)) => {
            let dur = start.elapsed();
            let stdout = {
                let mut s = String::new();
                child.stdout.take().unwrap().read_to_string(&mut s).ok();
                s
            };
            if !status.success() {
                println!("{}: crash (exit {:?})", name, status.code());
                return BenchResult { file: name, suite: suite.into(), time_ms: dur.as_millis(), nodes: 0, is_empty: false, status: "crash" };
            }
            let line = stdout.trim();
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() >= 3 && parts[0] == "RESULT" {
                let is_empty: bool = parts[1].parse().unwrap_or(true);
                let nodes: u32 = parts[2].parse().unwrap_or(0);
                let sat_str = if is_empty { "empty" } else { "nonempty" };
                println!("{}: {}ms, {} nodes [{}]", name, dur.as_millis(), nodes, sat_str);
                BenchResult { file: name, suite: suite.into(), time_ms: dur.as_millis(), nodes, is_empty, status: "ok" }
            } else {
                println!("{}: bad output: {:?}", name, line);
                BenchResult { file: name, suite: suite.into(), time_ms: dur.as_millis(), nodes: 0, is_empty: false, status: "crash" }
            }
        }
        Ok(None) => {
            child.kill().ok();
            child.wait().ok();
            let dur = start.elapsed();
            println!("{}: timeout (>{}s)", name, timeout_secs);
            BenchResult { file: name, suite: suite.into(), time_ms: dur.as_millis(), nodes: 0, is_empty: false, status: "timeout" }
        }
        Err(e) => {
            println!("{}: wait error: {}", name, e);
            BenchResult { file: name, suite: suite.into(), time_ms: 0, nodes: 0, is_empty: false, status: "crash" }
        }
    }
}

fn write_results(results: &[BenchResult], timeout_secs: u64, path: &str) {
    let mut md = String::new();
    md.push_str("# gaston benchmark results (comparison only)\n\n");
    md.push_str("Benchmarks from the Gaston WS1S decision procedure (TACAS'17).\n");
    md.push_str("Source: https://github.com/tfiedor/gaston\n\n");
    md.push_str("**Semantics mismatch**: Gaston benchmarks use WS1S; our solver uses M2L-STR.\n");
    md.push_str("Results are NOT correctness-checked. This is for performance comparison only.\n\n");
    md.push_str("Only the `horn_leq` suites (0-4 quantifier alternations) are included.\n");
    md.push_str("The remaining 6 suites use MONA syntax features not in our parser\n");
    md.push_str("(comma-separated quantifier variables, `pred` definitions).\n\n");
    md.push_str(&format!("## configuration\n\n```\ntimeout={}s\n{}\n```\n\n", timeout_secs, RegexBuilder::config_string()));

    let solved: Vec<_> = results.iter().filter(|r| r.status == "ok").collect();
    let timeouts: Vec<_> = results.iter().filter(|r| r.status == "timeout").collect();
    let crashes: Vec<_> = results.iter().filter(|r| r.status == "crash").collect();

    md.push_str("## summary\n\n");
    md.push_str(&format!("- total: {}\n", results.len()));
    md.push_str(&format!("- solved: {}\n", solved.len()));
    md.push_str(&format!("- timeout: {}\n", timeouts.len()));
    md.push_str(&format!("- crash: {}\n\n", crashes.len()));

    // per-suite summary
    md.push_str("| suite | files | solved | timeout | crash | total time (ms) |\n");
    md.push_str("|-------|-------|--------|---------|-------|-----------------|\n");
    for suite in SUITES {
        let suite_results: Vec<_> = results.iter().filter(|r| r.suite == *suite).collect();
        let s = suite_results.iter().filter(|r| r.status == "ok").count();
        let t = suite_results.iter().filter(|r| r.status == "timeout").count();
        let c = suite_results.iter().filter(|r| r.status == "crash").count();
        let total_ms: u128 = suite_results.iter().filter(|r| r.status == "ok").map(|r| r.time_ms).sum();
        md.push_str(&format!("| {} | {} | {} | {} | {} | {} |\n", suite, suite_results.len(), s, t, c, total_ms));
    }
    md.push_str("\n");

    if !timeouts.is_empty() {
        md.push_str("## timeouts\n\n| suite | file |\n|-------|------|\n");
        for r in &timeouts { md.push_str(&format!("| {} | {} |\n", r.suite, r.file)); }
        md.push_str("\n");
    }
    if !crashes.is_empty() {
        md.push_str("## crashes\n\n| suite | file |\n|-------|------|\n");
        for r in &crashes { md.push_str(&format!("| {} | {} |\n", r.suite, r.file)); }
        md.push_str("\n");
    }

    md.push_str("## results\n\n");
    md.push_str("| suite | file | time (ms) | nodes | result |\n");
    md.push_str("|-------|------|-----------|-------|--------|\n");
    for r in &solved {
        let result = if r.is_empty { "empty" } else { "nonempty" };
        md.push_str(&format!("| {} | {} | {} | {} | {} |\n", r.suite, r.file, r.time_ms, r.nodes, result));
    }
    let total_time: u128 = solved.iter().map(|r| r.time_ms).sum();
    let total_nodes: u64 = solved.iter().map(|r| r.nodes as u64).sum();
    md.push_str(&format!("| | **total** | **{}** | **{}** | |\n", total_time, total_nodes));

    let resolved = Path::new(path);
    fs::create_dir_all(resolved.parent().unwrap()).ok();
    fs::write(resolved, md).expect("failed to write results");
    println!("wrote {}", resolved.display());
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.get(1).map(|s| s.as_str()) == Some("--run-single") {
        let file = args.get(2).expect("missing file argument for --run-single");
        run_single(file);
        return;
    }

    let timeout: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(30);

    println!("gaston benchmarks (comparison only, WS1S != M2L-STR)");
    println!("suites: {:?}, timeout: {}s\n", SUITES, timeout);

    let mut all_results = Vec::new();

    for suite in SUITES {
        println!("=== {} ===", suite);
        let files = get_suite_files(suite);
        for file in &files {
            all_results.push(run_file_subprocess(suite, file, timeout));
        }

        let suite_results: Vec<_> = all_results.iter().filter(|r| r.suite == *suite).collect();
        let solved = suite_results.iter().filter(|r| r.status == "ok").count();
        let timeouts = suite_results.iter().filter(|r| r.status == "timeout").count();
        let crashes = suite_results.iter().filter(|r| r.status == "crash").count();
        println!(
            "--- {}: {}/{} solved, {} timeout, {} crash\n",
            suite, solved, suite_results.len(), timeouts, crashes
        );
    }

    write_results(&all_results, timeout, "results/benchmarks_gaston.md");
}
