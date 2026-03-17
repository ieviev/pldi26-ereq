// configuration sensitivity experiment.
//
// 10 formulas that timeout (>60s) under the default configuration.
// no single configuration solves all 10, but the union of three
// non-default configurations (dnf, then_first, no_compl_contains+then_first)
// covers all of them. this demonstrates that solver heuristics have a
// qualitative effect on which formulas are tractable.
//
// running all benchmarks (L10--L100) under every configuration takes >1 week.
// for a quicker review, run L10 and L20 (`just l10` / `just l20`) which
// complete in minutes and already exhibit configuration sensitivity.
//
// locally:
//   cargo run --release --example config_experiment -p tests

use std::{
    fs::read_to_string,
    path::Path,
    process::{Command, Stdio},
    sync::mpsc,
    thread,
    time::Duration,
};

use ereq::{MSO, RegexBuilder};

const TIMEOUT_SECS: u64 = 4;

#[allow(dead_code)]
struct Case {
    path: &'static str,
    // configs that solve this case (discovered empirically):
    // "default", "dnf", "low_cost_simplify", "dnf+low_cost_simplify"
    solved_by: &'static [&'static str],
}

// 10 hard cases not solved by default config. all solvable by some config.
//   default:  0/10
//   dnf:      form128, form155, form33, form355, form464, form489   (6/10)
//   tf:       form319, form51, N4L30.form104                        (3/10)
//   ncc+tf:   N4L30.form1                                           (1/10)
//   union:    10/10
const CASES: &[Case] = &[
    Case { path: "data/random/P0.5N4L20.form128.mona", solved_by: &["dnf"] },
    Case { path: "data/random/P0.5N4L20.form155.mona", solved_by: &["dnf"] },
    Case { path: "data/random/P0.5N4L20.form33.mona", solved_by: &["dnf"] },
    Case { path: "data/random/P0.5N4L20.form355.mona", solved_by: &["dnf"] },
    Case { path: "data/random/P0.5N4L20.form464.mona", solved_by: &["dnf"] },
    Case { path: "data/random/P0.5N4L20.form489.mona", solved_by: &["dnf"] },
    Case { path: "data/random/P0.5N4L20.form319.mona", solved_by: &["then_first"] },
    Case { path: "data/random/P0.5N4L20.form51.mona", solved_by: &["then_first"] },
    Case { path: "data/random/P0.5N4L30.form104.mona", solved_by: &["then_first"] },
    Case { path: "data/random/P0.5N4L30.form1.mona", solved_by: &["no_compl_contains+then_first"] },
];

// config names match binary suffixes in docker
const CONFIGS: &[&str] = &["default", "dnf", "lcs", "dnf+lcs", "nis", "tf", "tf+lcs"];

fn binary_for_config(config: &str) -> String {
    match config {
        "default" => "config-experiment-default".into(),
        "dnf" => "config-experiment-dnf".into(),
        "lcs" => "config-experiment-lcs".into(),
        "dnf+lcs" => "config-experiment-dnf-lcs".into(),
        "nis" => "config-experiment-nis".into(),
        "tf" => "config-experiment-tf".into(),
        "tf+lcs" => "config-experiment-tf-lcs".into(),
        _ => panic!("unknown config: {config}"),
    }
}

fn run_subprocess(exe: &str, path: &str, timeout: u64) -> (String, Option<u64>, Option<u32>) {
    // run-limited sets ulimit -v (2GB) + timeout with SIGKILL
    let output = Command::new("run-limited")
        .args([&timeout.to_string(), exe, "--run-single", path])
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .output();

    match output {
        Ok(out) if out.status.success() => {
            let text = String::from_utf8_lossy(&out.stdout);
            if let Some(line) = text.lines().find(|l| l.starts_with("RESULT")) {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() >= 3 {
                    let ms: u64 = parts[1].parse().unwrap_or(0);
                    let nodes: u32 = parts[2].parse().unwrap_or(0);
                    return ("ok".into(), Some(ms), Some(nodes));
                }
            }
            ("crash".into(), None, None)
        }
        Ok(_) => ("timeout".into(), None, None),
        Err(_) => ("missing".into(), None, None),
    }
}

fn run_single(path: &str) {
    let content = read_to_string(path).expect("failed to read file");
    let (tx, rx) = mpsc::channel();
    const STACK_SIZE: usize = 64 * 1024 * 1024;
    thread::Builder::new()
        .name("solver".into())
        .stack_size(STACK_SIZE)
        .spawn(move || {
            let mut mso = MSO::new();
            let constraints = mso.parse_mona_m2l_str(&content).expect("failed to parse");
            let start = std::time::Instant::now();
            let result = mso.b().is_empty_lang(constraints);
            let elapsed = start.elapsed();
            let nodes = mso.b().node_count();
            tx.send((result, nodes, elapsed)).ok();
        })
        .unwrap();

    match rx.recv_timeout(Duration::from_secs(TIMEOUT_SECS + 2)) {
        Ok((_is_empty, nodes, elapsed)) => {
            println!("RESULT {} {} {}", elapsed.as_millis(), nodes, _is_empty);
        }
        Err(_) => std::process::exit(1),
    }
}

fn run_single_config(_path: &str) {
    let config = RegexBuilder::config_string();
    println!("=== configuration experiment (single config) ===");
    println!("config: {}", config);
    println!("timeout: {}s", TIMEOUT_SECS);
    println!("{:<35} {:>8} {:>10}", "formula", "time", "nodes");
    println!("{}", "-".repeat(56));

    let exe = std::env::current_exe().unwrap();
    let exe = exe.to_str().unwrap();
    let mut solved = 0;

    for case in CASES {
        let name = Path::new(case.path).file_name().unwrap().to_str().unwrap();
        let (status, ms, nodes) = run_subprocess(exe, case.path, TIMEOUT_SECS);
        if status == "ok" {
            solved += 1;
            println!(
                "{:<35} {:>6}ms {:>10}",
                name,
                ms.unwrap_or(0),
                nodes.unwrap_or(0)
            );
        } else {
            println!("{:<35} {:>8}", name, status);
        }
    }

    println!("{}", "-".repeat(56));
    println!("solved: {}/{}", solved, CASES.len());
}

fn run_all_configs() {
    println!("=== configuration experiment (all configs) ===");
    println!("timeout: {}s", TIMEOUT_SECS);
    println!();

    // header
    print!("{:<35}", "formula");
    for config in CONFIGS {
        print!(" {:>12}", config);
    }
    println!();
    println!("{}", "-".repeat(35 + CONFIGS.len() * 13));

    let mut totals = vec![0usize; CONFIGS.len()];

    for case in CASES {
        let name = Path::new(case.path).file_name().unwrap().to_str().unwrap();
        print!("{:<35}", name);

        for (i, config) in CONFIGS.iter().enumerate() {
            let bin = binary_for_config(config);
            let (status, ms, _nodes) = run_subprocess(&bin, case.path, TIMEOUT_SECS);
            if status == "ok" {
                totals[i] += 1;
                print!(" {:>10}ms", ms.unwrap_or(0));
            } else if status == "missing" {
                print!(" {:>12}", "-");
            } else {
                print!(" {:>12}", "TO");
            }
        }
        println!();
    }

    println!("{}", "-".repeat(35 + CONFIGS.len() * 13));
    print!("{:<35}", "solved");
    for (i, _) in CONFIGS.iter().enumerate() {
        print!(" {:>9}/{:<2}", totals[i], CASES.len());
    }
    println!();
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.get(1).map(|s| s.as_str()) == Some("--run-single") {
        let file = args.get(2).expect("missing file argument");
        run_single(file);
        return;
    }

    // if multi-config binaries exist (docker), run all configs
    if Command::new("config-experiment-default")
        .arg("--help")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok()
    {
        run_all_configs();
    } else {
        // local: run with whatever config this binary was built with
        run_single_config("");
    }
}
