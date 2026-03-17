# Artifact Evaluation Guide

## Overview

EREQ is an M2L-STR satisfiability solver based on symbolic extended regular expressions with derivatives. This artifact reproduces the experiments from Section 8.2 of the paper, comparing EREQ against MONA on structured and random M2L-STR benchmarks.

**Submission vs final version.** The submitted paper evaluated two structured benchmark families (lift, counter) and the distance benchmark. Following mandatory revisions, the final version expands the evaluation to the full AutomatArk M2L-STR/LTL-finite benchmark set: lift (8), lift_b (8), counter (15), counter_l (15), and szymanski (4) -- 50 structured benchmarks in total, with cactus plots added. The artifact supports both the original claims and the expanded evaluation. Table and figure references below use the submission numbering.

## Requirements

- Docker (tested with Docker 24+)
- ~1GB disk for the container image
- 16GB RAM recommended
- Single core is sufficient; no parallelism required
- Reported timings were measured on an AMD Ryzen 5800X
- **Important:** MONA will consume all available memory on several benchmarks (it exhausted 128GB in our tests). The container wraps MONA with a 16GB virtual memory limit (`mona-limited`, via `ulimit -v`; Dockerfile line 57). Adjust via `MONA_MEM_LIMIT_KB` environment variable if needed. OOM kills are reported as "oom" in benchmark results.

## Claims Supported by the Artifact

| Claim | Paper reference | Artifact command |
|-------|----------------|------------------|
| EREQ solves lift_2 through lift_9; MONA fails at lift_5+ (OOM) | Table 2 | `run-ltlf.sh --timeout 60` |
| EREQ solves counter_2 through counter_16; MONA fails at counter_12+ | Table 3 | `run-ltlf.sh --timeout 60` |
| EREQ solves distance_2 through distance_20; MONA hits BDD limit at n=20 | Table 4 | `distance-bench 20` |
| No single rewrite configuration dominates; different configs solve different subsets | Section 8.2 | `config-experiment-sh` |
| *(final version)* EREQ solves all 50 structured LTL-F benchmarks; MONA solves 30/50 | -- | `run-ltlf.sh --timeout 60` |

The full AutomatArk M2L-STR suite used in the paper contains 10048 benchmarks: 9998 random + 50 structured LTL-F. On the full suite with a 60s timeout, MONA times out on 89 and EREQ in its best configuration times out on ~250. We do not claim superiority over MONA on random benchmarks. The artifact includes commands to run subsets of these benchmarks to validate correctness (all results match MONA ground truth where both finish). Full reproduction is optional and takes up to a week; running L10 (~2 minutes) is sufficient for validation.

## Claims Not Supported by the Artifact

- **Lean proofs** (Sections 5-6): the formalization is in a separate repository, not included in this artifact.
- **Full random benchmark reproduction**: reproducing all 9998 random benchmarks from scratch with a 60s timeout takes up to a week. Running L10 (~2 minutes) validates correctness against MONA ground truth. The cactus plot in the final version uses pre-recorded timing data.
- **Exact timings**: runtime numbers will vary by hardware. Relative performance between EREQ and MONA should be consistent.

## Correctness Notes

**Empty string semantics.** MONA's M2L-STR interpretation requires nonempty strings. EREQ operates over all strings including the empty string, so universal quantification (`all1`) can be vacuously satisfied on the empty string. To match MONA's semantics, EREQ intersects formulas with `~(ε)` (nonempty string). The `forall-experiment` command in the container demonstrates this difference and confirms that EREQ and MONA agree when the nonempty constraint is applied.

**Rewrite rules.** The expression simplification rules in the solver (Section 6) have been extensively tested across all benchmark families but have not yet been formally verified in Lean. The Lean formalization (Sections 5-6) covers the core theory -- derivatives, complement, and emptiness -- but does not yet extend to the full set of rewrite rules used by the implementation. This is a research prototype and may contain bugs. All structured LTL-F benchmarks agree with MONA, and the random benchmarks are validated against MONA ground truth where both solvers finished, with no disagreements.

## Getting Started Guide (~7 minutes)

### Loading the Container

A prebuilt Docker image is included in the Zenodo archive as `ereq-docker.tar.gz`:

```sh
docker load < ereq-docker.tar.gz
```

Alternatively, build from source (~5-15 minutes). The MONA submodule must be initialized first:

```sh
git submodule update --init
docker build -t ereq .
```

### Structured Benchmarks (~10 minutes)

> **Warning:** this command runs MONA, which will attempt to allocate unbounded memory on several benchmarks (it exhausted 128GB in our tests). Inside the container, MONA is wrapped with a 16GB virtual memory limit (`mona-limited`). If your machine has less than 16GB free, lower the limit: `docker run -e MONA_MEM_LIMIT_KB=8388608 ...` (8GB). Running outside the container without `mona-limited` risks triggering the OOM killer.

Run all 50 structured LTL-F benchmarks for both EREQ and MONA, and generate the cactus plot:

```sh
docker run -v ./results:/ereq/results -v ./plots:/ereq/plots ereq run-ltlf.sh --timeout 60
```

This runs EREQ and MONA on all 50 structured instances, writes timing data, and generates `plots/figs/cactus-structured.pdf`.

**Expected results:**
- **lift** (Table 2): EREQ solves all 8 (lift_9: ~1-3s). MONA solves lift_2 through lift_4, fails on lift_5+ (automaton state explosion).
- **lift_b** *(final version)*: EREQ 8/8 solved. MONA fails on lift_b_5+.
- **counter** (Table 3): EREQ solves all 15 (~4ms to ~35ms). MONA solves counter_2 through counter_11, fails on counter_12+ (BDD too large). At counter_11, EREQ is ~200x faster.
- **counter_l** *(final version)*: EREQ 15/15 solved. MONA fails on counter_l_12+.
- **szymanski** *(final version)*: both solve all 4. MONA is faster on these instances.
- **distance** (Table 4): both solve through n=19. MONA hits its BDD size limit at n=20.

Structured benchmark results are written to `results/comparison/structured_t60s.md`.

Distance is run separately (both EREQ and MONA), with EREQ results written to `results/benchmarks_distance.md`:

```sh
docker run -v ./results:/ereq/results ereq distance-bench 20
```

## Step-by-Step Instructions

### Step 1: Random Benchmark Correctness Validation (~2 minutes)

Run L10 random benchmarks (1000 formulas) to validate that EREQ results match MONA ground truth:

```sh
docker run -v ./results:/ereq/results ereq run-random.sh
```

This runs EREQ on N2L10 + N4L10 (500 formulas each) and checks results against pre-recorded MONA ground truth. The purpose is to validate correctness, not to reproduce the full random benchmark evaluation.

**Expected results:** 1000/1000 solved, 0 wrong, 0 timeout.

Optionally, run L20 (~15 minutes) for additional validation:

```sh
docker run -v ./results:/ereq/results ereq bash -c '
  benchmarks-random "N2L20." 30 --subprocess &&
  benchmarks-random "N4L20." 30 --subprocess
'
```

**Expected L20 results:** N2L20: 500/500 solved. N4L20: ~470/500 solved, ~30 timeout, 0 wrong.

### Step 2: Configuration Experiment (Section 8.2) (~10 seconds)

The solver has several compile-time configuration knobs (DNF mode, simplification cost thresholds, ITE branch exploration order, etc.) that trade performance between formula families. This experiment runs 3 representative hard cases against 3 configurations (default, dnf, then_first):

```sh
docker run ereq config-experiment-sh
```

**Expected output:** a table showing that `dnf` solves form128 but not form319, `tf` (then_first) solves form319 but not form128, and the default configuration solves neither. No single configuration solves all cases. This demonstrates that ITE branch exploration order and normal form choice have a qualitative effect on which formulas are tractable.

This ability to switch between expression rewriting strategies is unique to the derivative-based approach. MONA's BDD-based automata construction has no analogous knob -- it commits to a single canonical representation and cannot trade performance between formula families.

### Step 3: Additional Random Benchmark Levels (optional)

Additional levels can be run to further validate correctness across harder formulas:

```sh
docker run -v ./results:/ereq/results ereq bench-all
```

This runs L10--L100 with a 6s timeout. At higher levels (L40+), most formulas time out. Results for each level are written to `results/benchmarks_random_N{2,4}L{level}.md`.

For a longer timeout (60s, matching the paper), use `bench-all --long`. With 20 suites total (10 levels x N2 + N4), the full run can take **up to a week** -- this is not expected for evaluation.

## Interpreting Results

Each result file is a markdown table with:
- solver configuration (constants, flags)
- per-formula timing and node count
- summary: solved/timeout/wrong counts

### Gaston Horn Clause Benchmarks (comparison only)

The [Gaston](https://github.com/tfiedor/gaston) WS1S decision procedure (TACAS'17) provides generated benchmark suites of horn clause formulas with varying quantifier alternation depths. **The comparison is not equivalent**: Gaston benchmarks use WS1S semantics while our solver uses M2L-STR. The two logics differ in how second-order variables are interpreted (arbitrary sets vs finite sets), so emptiness/satisfiability results are not expected to agree. We include these benchmarks for comparison only.

Of the 11 Gaston suites (202 files total), our parser supports 5 -- the `horn_leq` family with 0 through 4 quantifier alternations (92 files). The remaining 6 suites (`horn_in`, `horn_trans`, `set_closed`, `set_obvious`, `set_singletons`, `strand`) use MONA syntax features not in our parser.

```sh
docker run -v ./results:/ereq/results ereq gaston-bench 30
```

**Expected results:** 92/92 files solved (0 timeout, 0 crash) across all 5 suites. Results are written to `results/benchmarks_gaston.md`.

## Running Outside Docker

A Nix flake (`flake.nix`) is provided as an alternative to Docker. It sets up Rust nightly, MONA, Node.js, and jq via `nix develop`. This is optional and not required for evaluation.

Requires Rust nightly:

```sh
rustup override set nightly
cargo build --release --features profile --examples

# lift and counter
cargo run --release --example benchmarks --features profile -- lift
cargo run --release --example benchmarks --features profile -- counter

# distance (requires low_cost_simplify + low_high_limit features)
cargo run --release --features low_cost_simplify,low_high_limit --example distance -p ereq -- 20

# random benchmarks
cargo run --release --example benchmarks-random -- "N2L10." 30

# generate plots (requires node.js)
cd plots && npm install && npm run all
```

The `profile` feature enables optional diagnostic output and does not affect solver behavior.

## Source Code Structure

```
src/
  ereq-algebra/   core symbolic regex algebra: derivatives, simplification, emptiness
  ereq/              MSO frontend: MONA M2L-STR parser, MSO-to-regex translation, benchmarks
data/
  lift/              lift and lift_b property benchmark formulas (16)
  counter/           counter and counter_l LTL property benchmark formulas (30)
  szymanski/         szymanski mutual exclusion benchmark formulas (4)
  random/            randomly generated MSO formulas (9998)
  result-sat.txt     pre-recorded MONA ground truth (sat, 8796 formulas)
  result-unsat.txt   pre-recorded MONA ground truth (unsat, 1159 formulas)
  gaston/            Gaston WS1S horn clause benchmarks (comparison only, 202 files)
plots/
  gen-cactus.mjs     cactus plot generator (node.js, d3 + pdfkit)
  prerecorded/       pre-recorded MONA and EREQ timing data for cactus plots
  data/              output directory for fresh benchmark timing data
```
