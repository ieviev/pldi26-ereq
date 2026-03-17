use std::{
    collections::HashSet,
    fs::{self, read, read_dir},
    io::BufRead,
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

struct MonaResults {
    sat: HashSet<String>,
    unsat: HashSet<String>,
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
        unsat: mona_unsat,
    }
}

fn get_benchmark_files(filter: &str) -> Vec<String> {
    let dir = base().join("../../data/random/");
    let mut files = Vec::new();
    for entry in read_dir(dir).expect("failed to read data/random/") {
        let entry = entry.unwrap();
        let name = entry.file_name().to_string_lossy().to_string();
        if name.contains(filter) {
            files.push(entry.path().to_string_lossy().to_string());
        }
    }
    files.sort();
    files
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

struct BenchResult {
    file: String,
    time_ms: u128,
    nodes: u32,
    status: &'static str, // "ok", "timeout", "wrong", "crash"
}

fn run_file(expected: &MonaResults, file: &str, timeout_secs: u64) -> BenchResult {
    let pbuf = PathBuf::from(file);
    let name = pbuf.file_name().unwrap().to_str().unwrap().to_string();
    let content = fs::read_to_string(file).expect("failed to read input file");

    let start = std::time::Instant::now();
    let (tx, rx) = mpsc::channel();
    let input = content.clone();
    thread::spawn(move || tx.send(check_ereq_emptiness(input)));

    match rx.recv_timeout(Duration::from_secs(timeout_secs)) {
        Ok((is_empty, nodes)) => {
            let dur = std::time::Instant::now().duration_since(start);
            let mona_sat = expected.sat.contains(name.as_str());
            let mona_unsat = expected.unsat.contains(name.as_str());
            let status = if mona_sat || mona_unsat {
                if !is_empty == mona_sat { "ok" } else { "wrong" }
            } else {
                "ok" // mona also timed out, can't verify
            };
            if status == "wrong" {
                eprintln!(
                    "WRONG: {} (got {}, mona={})",
                    name,
                    if !is_empty { "sat" } else { "unsat" },
                    if mona_sat { "sat" } else { "unsat" }
                );
            }
            println!(
                "{}: {}ms, {} nodes [{}]",
                name,
                dur.as_millis(),
                nodes,
                status
            );
            BenchResult {
                file: name,
                time_ms: dur.as_millis(),
                nodes,
                status,
            }
        }
        Err(_) => {
            let dur = std::time::Instant::now().duration_since(start);
            println!("{}: timeout (>{}s)", name, timeout_secs);
            BenchResult {
                file: name,
                time_ms: dur.as_millis(),
                nodes: 0,
                status: "timeout",
            }
        }
    }
}

/// run a single file as a subprocess to isolate stack overflows and memory leaks.
/// the subprocess re-invokes this binary with --run-single <file>.
fn run_file_subprocess(expected: &MonaResults, file: &str, timeout_secs: u64) -> BenchResult {
    let pbuf = PathBuf::from(file);
    let name = pbuf.file_name().unwrap().to_str().unwrap().to_string();

    let start = std::time::Instant::now();
    let exe = std::env::current_exe().unwrap();
    let child = Command::new(&exe)
        .args(["--run-single", file])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn();

    let mut child = match child {
        Ok(c) => c,
        Err(e) => {
            println!("{}: spawn error: {}", name, e);
            return BenchResult {
                file: name,
                time_ms: 0,
                nodes: 0,
                status: "crash",
            };
        }
    };

    let timeout = Duration::from_secs(timeout_secs);
    match child.wait_timeout(timeout) {
        Ok(Some(status)) => {
            let dur = std::time::Instant::now().duration_since(start);
            let stdout = {
                use std::io::Read;
                let mut s = String::new();
                child.stdout.take().unwrap().read_to_string(&mut s).ok();
                s
            };
            if !status.success() {
                println!("{}: crash (exit {:?})", name, status.code());
                return BenchResult {
                    file: name,
                    time_ms: dur.as_millis(),
                    nodes: 0,
                    status: "crash",
                };
            }
            // parse output: "RESULT <is_empty> <nodes>"
            let parts: Vec<&str> = stdout.trim().split_whitespace().collect();
            if parts.len() >= 3 && parts[0] == "RESULT" {
                let is_empty: bool = parts[1].parse().unwrap_or(true);
                let nodes: u32 = parts[2].parse().unwrap_or(0);

                let mona_sat = expected.sat.contains(name.as_str());
                let mona_unsat = expected.unsat.contains(name.as_str());
                let status = if mona_sat || mona_unsat {
                    if !is_empty == mona_sat { "ok" } else { "wrong" }
                } else {
                    "ok"
                };
                if status == "wrong" {
                    eprintln!(
                        "WRONG: {} (got {}, mona={})",
                        name,
                        if !is_empty { "sat" } else { "unsat" },
                        if mona_sat { "sat" } else { "unsat" }
                    );
                }
                println!(
                    "{}: {}ms, {} nodes [{}]",
                    name,
                    dur.as_millis(),
                    nodes,
                    status
                );
                BenchResult {
                    file: name,
                    time_ms: dur.as_millis(),
                    nodes,
                    status,
                }
            } else {
                println!("{}: bad output: {:?}", name, stdout.trim());
                BenchResult {
                    file: name,
                    time_ms: dur.as_millis(),
                    nodes: 0,
                    status: "crash",
                }
            }
        }
        Ok(None) => {
            // timeout - kill the child
            child.kill().ok();
            child.wait().ok();
            let dur = std::time::Instant::now().duration_since(start);
            println!("{}: timeout (>{}s)", name, timeout_secs);
            BenchResult {
                file: name,
                time_ms: dur.as_millis(),
                nodes: 0,
                status: "timeout",
            }
        }
        Err(e) => {
            println!("{}: wait error: {}", name, e);
            BenchResult {
                file: name,
                time_ms: 0,
                nodes: 0,
                status: "crash",
            }
        }
    }
}

/// single-file mode: solve one file and print result to stdout.
/// profile output goes to stderr via print_profile(), only RESULT goes to stdout.
fn run_single(file: &str) {
    let content = fs::read_to_string(file).expect("failed to read input file");
    const STACK_SIZE: usize = 1024 * 1024 * 1024;
    let (tx, rx) = mpsc::channel();
    thread::Builder::new()
        .name("solver".into())
        .stack_size(STACK_SIZE)
        .spawn(move || {
            let mut mso: MSO = MSO::new();
            let t0 = std::time::Instant::now();
            let constraints = mso.parse_mona_m2l_str(&content).expect("failed to parse");
            let init_nodes = mso.b().node_count();
            let t1 = std::time::Instant::now();
            let result = mso.b().is_empty_lang(constraints);
            let t2 = std::time::Instant::now();
            let nodes = mso.b().node_count();
            eprintln!(
                "PROFILE init={}ms ({}nodes) empty={}ms ({}nodes created)",
                t1.duration_since(t0).as_millis(),
                init_nodes,
                t2.duration_since(t1).as_millis(),
                nodes - init_nodes
            );
            mso.b().print_profile();
            tx.send((result, nodes))
        })
        .unwrap();
    let (is_empty, nodes) = rx.recv().unwrap();
    println!("RESULT {} {}", is_empty, nodes);
}

fn write_results(suite: &str, results: &[BenchResult], path: &str) {
    let mut md = String::new();

    let solved: Vec<_> = results.iter().filter(|r| r.status == "ok").collect();
    let timeouts: Vec<_> = results.iter().filter(|r| r.status == "timeout").collect();
    let wrong: Vec<_> = results.iter().filter(|r| r.status == "wrong").collect();
    let crashes: Vec<_> = results.iter().filter(|r| r.status == "crash").collect();

    md.push_str(&format!("# {} benchmark results\n\n", suite));
    md.push_str(&format!(
        "## configuration\n\n```\n{}\n```\n\n",
        RegexBuilder::config_string()
    ));
    md.push_str(&format!("## summary\n\n"));
    md.push_str(&format!("- total: {}\n", results.len()));
    md.push_str(&format!("- solved: {}\n", solved.len()));
    md.push_str(&format!("- timeout: {}\n", timeouts.len()));
    md.push_str(&format!("- crash: {}\n", crashes.len()));
    md.push_str(&format!("- wrong: {}\n\n", wrong.len()));

    if !wrong.is_empty() {
        md.push_str("## wrong results\n\n");
        md.push_str("| file |\n|------|\n");
        for r in &wrong {
            md.push_str(&format!("| {} |\n", r.file));
        }
        md.push_str("\n");
    }

    if !crashes.is_empty() {
        md.push_str("## crashes\n\n");
        md.push_str("| file |\n|------|\n");
        for r in &crashes {
            md.push_str(&format!("| {} |\n", r.file));
        }
        md.push_str("\n");
    }

    if !timeouts.is_empty() {
        md.push_str("## timeouts\n\n");
        md.push_str("| file |\n|------|\n");
        for r in &timeouts {
            md.push_str(&format!("| {} |\n", r.file));
        }
        md.push_str("\n");
    }

    md.push_str("## solved\n\n");
    md.push_str("| file | time (ms) | nodes |\n");
    md.push_str("|------|-----------|-------|\n");
    for r in &solved {
        md.push_str(&format!("| {} | {} | {} |\n", r.file, r.time_ms, r.nodes));
    }
    let total_time: u128 = solved.iter().map(|r| r.time_ms).sum();
    let total_nodes: u64 = solved.iter().map(|r| r.nodes as u64).sum();
    md.push_str(&format!(
        "| **total** | **{}** | **{}** |\n",
        total_time, total_nodes
    ));

    let resolved = Path::new(path);
    fs::create_dir_all(resolved.parent().unwrap()).ok();
    fs::write(&resolved, md).expect("failed to write results");
    println!("wrote {}", resolved.display());
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    // subprocess mode: solve a single file
    if args.get(1).map(|s| s.as_str()) == Some("--run-single") {
        let file = args.get(2).expect("missing file argument for --run-single");
        run_single(file);
        return;
    }

    let filter = args.get(1).map(|s| s.as_str()).unwrap_or("L10.");
    let timeout: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(10);
    let limit: usize = args
        .get(3)
        .and_then(|s| s.parse().ok())
        .unwrap_or(usize::MAX);
    let use_subprocess = args.iter().any(|s| s == "--subprocess");

    println!(
        "=== random benchmarks (filter={}, timeout={}s, limit={}{}) ===",
        filter,
        timeout,
        if limit == usize::MAX {
            "all".to_string()
        } else {
            limit.to_string()
        },
        if use_subprocess { ", subprocess" } else { "" }
    );

    let mut files = get_benchmark_files(filter);
    files.truncate(limit);
    println!("running {} files", files.len());

    let expected = get_mona_results_prerecorded();
    let mut results = Vec::new();

    for file in &files {
        let r = if use_subprocess {
            run_file_subprocess(&expected, file, timeout)
        } else {
            run_file(&expected, file, timeout)
        };
        results.push(r);
    }

    let solved = results.iter().filter(|r| r.status == "ok").count();
    let timeouts = results.iter().filter(|r| r.status == "timeout").count();
    let wrong = results.iter().filter(|r| r.status == "wrong").count();
    let crashes = results.iter().filter(|r| r.status == "crash").count();
    println!(
        "\n=== summary: {}/{} solved, {} timeout, {} crash, {} wrong ===",
        solved,
        results.len(),
        timeouts,
        crashes,
        wrong
    );

    let output = format!("results/benchmarks_random_{}.md", filter.trim_matches('.'));
    write_results(&format!("random ({})", filter), &results, &output);
}
