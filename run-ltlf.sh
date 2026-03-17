#!/usr/bin/env bash
set -euo pipefail

# run all 50 LTL-F structured benchmarks for EREQ and MONA, generate cactus plot (Figure 5)
# usage: ./run-ltlf.sh [--timeout SECS] [--skip-mona] [--skip-ereq]
#
# each formula is run with a per-formula timeout (default 60s).
# MONA OOM/crash is caught by the timeout wrapper.
# output:
#   results/comparison/structured_t{T}s.md  - comparison table
#   plots/data/structured_ereq.json         - sorted EREQ times (seconds)
#   plots/data/structured_mona.json         - sorted MONA times (seconds)
#   plots/figs/cactus-structured.pdf        - cactus plot

ROOT=${EREQ_ROOT:-$(cd "$(dirname "$0")" && pwd)}
TIMEOUT=10
SKIP_MONA=false
SKIP_EREQ=false

while [[ $# -gt 0 ]]; do
    case "$1" in
        --timeout) TIMEOUT="$2"; shift 2 ;;
        --skip-mona) SKIP_MONA=true; shift ;;
        --skip-ereq) SKIP_EREQ=true; shift ;;
        *) echo "usage: $0 [--timeout SECS] [--skip-mona] [--skip-ereq]" >&2; exit 1 ;;
    esac
done

if [ "$SKIP_MONA" = false ]; then
    if command -v mona-limited &>/dev/null; then
        MONA_BIN=mona-limited
    elif command -v mona &>/dev/null; then
        MONA_BIN=mona
    else
        echo "error: mona not found on PATH" >&2
        exit 1
    fi
    echo "using mona: $(command -v $MONA_BIN)"
fi

# find or build EREQ binary
if [ "$SKIP_EREQ" = false ]; then
    if command -v benchmarks-random &>/dev/null; then
        EREQ_BIN="$(command -v benchmarks-random)"
    else
        echo "building ereq..."
        cargo build --release --example benchmarks-random 2>&1 | tail -1
        EREQ_BIN="$ROOT/target/release/examples/benchmarks-random"
    fi
    echo "using ereq: $EREQ_BIN"
fi

# find data directory
DATADIR="$ROOT/data"
[ -d "$DATADIR" ] || DATADIR="/ereq/data"
[ -d "$DATADIR" ] || { echo "error: data directory not found" >&2; exit 1; }

# all 50 structured benchmark files, in suite order
files=()
for i in 2 3 4 5 6 7 8 9; do
    files+=("$DATADIR/lift/lift_${i}.ltl0.mona")
done
for i in 2 3 4 5 6 7 8 9; do
    files+=("$DATADIR/lift/lift_b_${i}.ltl0.mona")
done
for i in $(seq 2 16); do
    files+=("$DATADIR/counter/counter_${i}.ltl0.mona")
done
for i in $(seq 2 16); do
    files+=("$DATADIR/counter/counter_l_${i}.ltl0.mona")
done
for f in "$DATADIR/szymanski/"*.mona; do
    files+=("$f")
done

n=${#files[@]}
echo "=== LTL-F structured benchmarks ($n files, ${TIMEOUT}s timeout) ==="

ereq_times_ms=()
mona_times_ms=()
rows=""

for file in "${files[@]}"; do
    fname=$(basename "$file")
    ereq_cell="-"
    mona_cell="-"

    # EREQ
    if [ "$SKIP_EREQ" = false ]; then
        start=$(date +%s%N)
        ereq_err=$(timeout "${TIMEOUT}s" "$EREQ_BIN" --run-single "$file" 2>&1) && rc=0 || rc=$?
        if [ $rc -eq 0 ]; then
            end=$(date +%s%N)
            ereq_ms=$(( (end - start) / 1000000 ))
            ereq_times_ms+=("$ereq_ms")
            ereq_cell="$ereq_ms"
        elif [ $rc -eq 124 ]; then
            ereq_cell="timeout"
        else
            ereq_cell="error($rc)"
            echo "    ereq stderr: $ereq_err" >&2
        fi
    fi

    # MONA
    if [ "$SKIP_MONA" = false ]; then
        start=$(date +%s%N)
        rc=0; timeout "${TIMEOUT}s" $MONA_BIN "$file" > /dev/null 2>&1 || rc=$?
        end=$(date +%s%N)
        mona_ms=$(( (end - start) / 1000000 ))
        if [ $rc -eq 0 ]; then
            mona_times_ms+=("$mona_ms")
            mona_cell="$mona_ms"
        elif [ $rc -eq 124 ]; then
            mona_cell="timeout"
        else
            mona_cell="oom"
        fi
    fi

    printf "  %-35s  ereq=%-8s  mona=%-8s\n" "$fname" "$ereq_cell" "$mona_cell"
    rows+="| $fname | $ereq_cell | $mona_cell |\n"
done

# comparison table
mkdir -p "$ROOT/results/comparison"
outfile="$ROOT/results/comparison/structured_t${TIMEOUT}s.md"
{
    echo "# LTL-F structured comparison (timeout=${TIMEOUT}s)"
    echo ""
    echo "| file | EREQ (ms) | MONA (ms) |"
    echo "|------|-----------|-----------|"
    echo -e "$rows"
    echo "## summary"
    echo ""
    echo "- EREQ: ${#ereq_times_ms[@]} / $n solved"
    echo "- MONA: ${#mona_times_ms[@]} / $n solved"
} > "$outfile"
echo ""
echo "wrote $outfile"

# JSON timing data (sorted ascending, in seconds)
sorted_json() {
    if [ $# -eq 0 ]; then echo "[]"; return; fi
    printf '%s\n' "$@" | sort -n | jq -s 'map(. / 1000 | . * 1000 | round / 1000)'
}

mkdir -p "$ROOT/plots/data"
sorted_json "${ereq_times_ms[@]}" > "$ROOT/plots/data/structured_ereq.json"
sorted_json "${mona_times_ms[@]}" > "$ROOT/plots/data/structured_mona.json"
echo "wrote plots/data/structured_ereq.json (${#ereq_times_ms[@]} solved)"
echo "wrote plots/data/structured_mona.json (${#mona_times_ms[@]} solved)"

# generate figure
cd "$ROOT/plots"
if [ ! -d node_modules ]; then
    echo "installing plot dependencies..."
    npm install --silent 2>&1 | tail -1
fi
node gen-cactus.mjs --structured
echo ""
echo "=== done: EREQ ${#ereq_times_ms[@]}/$n, MONA ${#mona_times_ms[@]}/$n ==="
echo "figure: plots/figs/cactus-structured.pdf"
