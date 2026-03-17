# EREQ

[![DOI](https://zenodo.org/badge/1184193701.svg)](https://doi.org/10.5281/zenodo.19072416)

An MSO (weak monadic second-order logic) satisfiability solver over finite words,
based on symbolic extended regular expressions with derivatives.

Instead of the classical BDD-based automata construction (as in MONA),
EREQ translates MSO formulas into extended regular expressions
(with intersection, complement, and existential quantification)
and decides emptiness via Brzozowski-style symbolic derivatives.

## Structure

```
src/
  ereq-algebra/      Core symbolic regex algebra: node construction, derivatives,
                     simplification, emptiness checking, BDD-backed predicates
  ereq/              MSO frontend: MONA M2L-STR parser, MSO-to-regex translation, benchmarks
```

## Building

Requires **nightly** Rust (for `portable_simd`):

```sh
git clone --recursive <repo-url>
cd ereq
rustup override set nightly
cargo build --release
```

If already cloned without `--recursive`, initialize the MONA submodule:

```sh
git submodule update --init
```

## Usage

### As a Library

```rust
use ereq::MSO;

let input = std::fs::read_to_string("formula.mona").unwrap();
let mut mso = MSO::new();
let node = mso.parse_mona_m2l_str(&input).expect("parse error");
let is_empty = mso.b().is_empty_lang(node);
println!("satisfiable: {}", !is_empty);
```

### Running Benchmarks

```sh
# Lift benchmarks (8 formulas from LTL-to-MSO translation)
cargo run --release --example benchmarks --features profile -- lift

# Counter benchmarks (15 LTL counter properties)
cargo run --release --example benchmarks --features profile -- counter

# Random MSO formulas (requires data/random/)
cargo run --release --example benchmarks-random -- "P0.5N2L10." 30
```

Results are written to `results/` as markdown tables.

### Docker

The container includes EREQ, [MONA](https://github.com/cs-au-dk/MONA) (v1.4-18), and all benchmark data.

MONA can consume unbounded memory on complex formulas.
Inside the container, `mona-limited` wraps MONA with a 16GB virtual memory limit
(override via `MONA_MEM_LIMIT_KB`) to prevent the OOM killer from
affecting the host. OOM kills are reported as "oom" in benchmark results.

```sh
docker build -t ereq .
docker run -it -v ./results:/ereq/results -v ./plots:/ereq/plots ereq
```

Inside the container:

```sh
# Comparison figure (EREQ vs MONA on all 50 structured LTL-F benchmarks)
run-ltlf.sh --timeout 60
# output: results/comparison/structured_t60s.md
#         plots/figs/cactus-structured.pdf

# EREQ benchmarks
benchmarks lift
benchmarks counter
benchmarks-random "P0.5N2L20." 30 --subprocess

# All random benchmarks L10-L100
bench-all                          # 6s timeout
bench-all 30 --long                # resume from L30, 60s timeout

# MONA benchmarks
mona-bench lift
mona-bench counter
```

### Input Format

EREQ accepts formulas in MONA's M2L-STR format:

```
m2l-str;
var1 x, y;
x < y & ex1 z: x < z & z < y;
```

## Benchmark Data

- `data/lift/` -- Lift property benchmarks (lift-2 through lift-9)
- `data/counter/` -- Counter LTL property benchmarks
- `data/random/` -- Randomly generated MSO formulas of varying size and quantifier depth

## Correctness

The MSO-to-EREQ translation and the derivative construction are
proven correct in Lean. The Rust implementation has not been formally
verified and features complex rewrite rules for performance
whose correctness we cannot fully guarantee.

**Forall on empty string**: MONA restricts M2L-STR to nonempty strings.
EREQ matches this by intersecting with `~(ε)` after translation.
Without this, universally quantified formulas can be vacuously
satisfied by the empty string.
In Docker: `forall-experiment` (runs both EREQ and MONA).

Correctness is validated against prerecorded MONA results in
`data/result-{sat,unsat}.txt`. Formulas where either solver timed out are not verified.

## License

[MIT](LICENSE)
