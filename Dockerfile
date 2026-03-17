FROM rustlang/rust:nightly-slim AS builder

RUN rustup target add x86_64-unknown-linux-musl \
 && apt-get update && apt-get install -y --no-install-recommends musl-tools && rm -rf /var/lib/apt/lists/*

ENV TARGET=x86_64-unknown-linux-musl
ENV CARGO_BUILD="cargo build --release --target $TARGET"
WORKDIR /ereq
COPY . .
RUN $CARGO_BUILD --examples \
 && $CARGO_BUILD --features profile --example benchmarks -p ereq \
 && $CARGO_BUILD --features low_cost_simplify,low_high_limit --example distance -p ereq \
 && $CARGO_BUILD --example forall_empty_string -p ereq \
 && $CARGO_BUILD --example benchmarks_gaston -p ereq \
 && $CARGO_BUILD --example config_experiment -p ereq \
 && cp target/$TARGET/release/examples/config_experiment target/$TARGET/release/examples/config-experiment-default \
 && $CARGO_BUILD --features dnf --example config_experiment -p ereq \
 && cp target/$TARGET/release/examples/config_experiment target/$TARGET/release/examples/config-experiment-dnf \
 && $CARGO_BUILD --features low_cost_simplify --example config_experiment -p ereq \
 && cp target/$TARGET/release/examples/config_experiment target/$TARGET/release/examples/config-experiment-lcs \
 && $CARGO_BUILD --features "dnf,low_cost_simplify" --example config_experiment -p ereq \
 && cp target/$TARGET/release/examples/config_experiment target/$TARGET/release/examples/config-experiment-dnf-lcs \
 && $CARGO_BUILD --features no_init_simplify --example config_experiment -p ereq \
 && cp target/$TARGET/release/examples/config_experiment target/$TARGET/release/examples/config-experiment-nis \
 && $CARGO_BUILD --features then_first --example config_experiment -p ereq \
 && cp target/$TARGET/release/examples/config_experiment target/$TARGET/release/examples/config-experiment-tf \
 && $CARGO_BUILD --features "then_first,low_cost_simplify" --example config_experiment -p ereq \
 && cp target/$TARGET/release/examples/config_experiment target/$TARGET/release/examples/config-experiment-tf-lcs

FROM debian:bookworm-slim AS mona-builder

RUN apt-get update && apt-get install -y --no-install-recommends build-essential autoconf automake flex bison && rm -rf /var/lib/apt/lists/*
COPY MONA/ /mona/
WORKDIR /mona
RUN ./configure && make && make install-strip DESTDIR=/mona-install

FROM node:22-slim

RUN apt-get update && apt-get install -y --no-install-recommends jq && rm -rf /var/lib/apt/lists/*

COPY --from=builder /ereq/target/x86_64-unknown-linux-musl/release/examples/benchmarks /usr/local/bin/benchmarks
COPY --from=builder /ereq/target/x86_64-unknown-linux-musl/release/examples/benchmarks-random /usr/local/bin/benchmarks-random
COPY --from=builder /ereq/target/x86_64-unknown-linux-musl/release/examples/distance /usr/local/bin/distance
COPY --from=builder /ereq/target/x86_64-unknown-linux-musl/release/examples/forall_empty_string /usr/local/bin/forall_empty_string
COPY --from=builder /ereq/target/x86_64-unknown-linux-musl/release/examples/benchmarks_gaston /usr/local/bin/benchmarks_gaston
COPY --from=builder /ereq/target/x86_64-unknown-linux-musl/release/examples/config_experiment /usr/local/bin/config-experiment
COPY --from=builder /ereq/target/x86_64-unknown-linux-musl/release/examples/config-experiment-default /usr/local/bin/config-experiment-default
COPY --from=builder /ereq/target/x86_64-unknown-linux-musl/release/examples/config-experiment-dnf /usr/local/bin/config-experiment-dnf
COPY --from=builder /ereq/target/x86_64-unknown-linux-musl/release/examples/config-experiment-lcs /usr/local/bin/config-experiment-lcs
COPY --from=builder /ereq/target/x86_64-unknown-linux-musl/release/examples/config-experiment-dnf-lcs /usr/local/bin/config-experiment-dnf-lcs
COPY --from=builder /ereq/target/x86_64-unknown-linux-musl/release/examples/config-experiment-nis /usr/local/bin/config-experiment-nis
COPY --from=builder /ereq/target/x86_64-unknown-linux-musl/release/examples/config-experiment-tf /usr/local/bin/config-experiment-tf
COPY --from=builder /ereq/target/x86_64-unknown-linux-musl/release/examples/config-experiment-tf-lcs /usr/local/bin/config-experiment-tf-lcs
COPY --from=mona-builder /mona-install/usr/local/ /usr/local/
RUN ldconfig

RUN printf '#!/bin/sh\nulimit -v "${MONA_MEM_LIMIT_KB:-16777216}"\nexec mona "$@"\n' \
    > /usr/local/bin/mona-limited && chmod +x /usr/local/bin/mona-limited

COPY data/ /ereq/data/
COPY plots/ /ereq/plots/
COPY run-ltlf.sh /usr/local/bin/run-ltlf.sh
RUN mkdir -p /ereq/src/ereq

WORKDIR /ereq/plots
RUN npm install --omit=dev 2>/dev/null

WORKDIR /ereq
ENV EREQ_ROOT=/ereq
RUN mkdir -p results

RUN printf '#!/bin/sh\nTIMEOUT="$1"; shift\nulimit -v 2097152 2>/dev/null\nexec timeout --kill-after=2s "${TIMEOUT}s" "$@"\n' \
    > /usr/local/bin/run-limited && chmod +x /usr/local/bin/run-limited

RUN cat <<'SCRIPT' > /usr/local/bin/bench-all && chmod +x /usr/local/bin/bench-all
#!/bin/sh
set -e
TIMEOUT=6
START=10
for arg in "$@"; do
  case "$arg" in
    --long) TIMEOUT=60 ;;
    *) START="$arg" ;;
  esac
done
for L in 10 20 30 40 50 60 70 80 90 100; do
  [ "$L" -lt "$START" ] && continue
  for N in 2 4; do
    echo "=== N${N}L${L} ==="
    benchmarks-random "N${N}L${L}." "$TIMEOUT" --subprocess || true
    echo ""
  done
done
SCRIPT

RUN cat <<'SCRIPT' > /usr/local/bin/mona-bench && chmod +x /usr/local/bin/mona-bench
#!/bin/bash
set -euo pipefail
trap 'exit 130' INT
SUITE=${1:-lift}
TIMEOUT=${2:-6}
OUTFILE="results/mona_${SUITE}.md"

echo "# mona ${SUITE} benchmark results" > "$OUTFILE"
echo "" >> "$OUTFILE"
echo "| file | time (ms) | result |" >> "$OUTFILE"
echo "|------|-----------|--------|" >> "$OUTFILE"

TOTAL_MS=0
SOLVED=0
FAILURES=0
COUNT=0
for f in $(ls data/${SUITE}/*.mona | sort -t_ -k2 -V); do
  NAME=$(basename "$f")
  COUNT=$((COUNT + 1))
  START=$(date +%s%N)
  TMPOUT=$(mktemp)
  timeout --foreground "$TIMEOUT" mona-limited "$f" > "$TMPOUT" 2>&1 && RC=0 || RC=$?
  MS=$(( ($(date +%s%N) - START) / 1000000 ))
  if [ "$RC" -eq 0 ]; then
    TOTAL_MS=$((TOTAL_MS + MS))
    SOLVED=$((SOLVED + 1))
    if grep -q "unsatisfiable\|valid" "$TMPOUT"; then
      R="unsat"
    else
      R="sat"
    fi
    echo "| ${NAME} | ${MS} | ${R} |" >> "$OUTFILE"
    echo "${NAME}: ${MS}ms [${R}]"
  elif [ "$RC" -eq 124 ] || [ "$RC" -eq 143 ]; then
    FAILURES=$((FAILURES + 1))
    echo "| ${NAME} | timeout (>${TIMEOUT}s) | |" >> "$OUTFILE"
    echo "${NAME}: timeout (>${TIMEOUT}s)"
  else
    FAILURES=$((FAILURES + 1))
    echo "| ${NAME} | ${MS}ms | oom/crash (rc=$RC) |" >> "$OUTFILE"
    echo "${NAME}: ${MS}ms [oom/crash rc=$RC]"
  fi
  rm -f "$TMPOUT"
done

echo "| **total** | **${TOTAL_MS}** | **${SOLVED}/${COUNT} solved, ${FAILURES} failed** |" >> "$OUTFILE"
echo "=== summary: ${SOLVED}/${COUNT} solved, ${FAILURES} failed ==="
echo "wrote ${OUTFILE}"
SCRIPT

RUN cat <<'SCRIPT' > /usr/local/bin/mona-distance && chmod +x /usr/local/bin/mona-distance
#!/bin/bash
set -euo pipefail
trap 'exit 130' INT
MAX_N=${1:-20}
TIMEOUT=${2:-15}

echo "mona distance benchmark: n=2..${MAX_N} (timeout ${TIMEOUT}s)"
printf "%-4s %-8s %-10s\n" "n" "result" "time (ms)"
printf '%s\n' "$(printf '%.0s-' {1..26})"

for n in $(seq 2 "$MAX_N"); do
  FORMULA=$(cat <<EOF
m2l-str;
var2 A;
(all1 x0: (x0 in A) <=> (ex1 x1: x1 = x0 + 1 & (x1 notin A)));
(0 in A);
(ex1 x0: (x0 in A) & (ex1 x1: (x1 = x0 + $n) & (x1 notin A)));
EOF
)
  TMPFILE=$(mktemp --suffix=.mona)
  echo "$FORMULA" > "$TMPFILE"
  START=$(date +%s%N)
  TMPOUT=$(mktemp)
  timeout --foreground "$TIMEOUT" mona-limited "$TMPFILE" > "$TMPOUT" 2>&1 && RC=0 || RC=$?
  MS=$(( ($(date +%s%N) - START) / 1000000 ))
  rm -f "$TMPFILE"
  if [ "$RC" -eq 0 ]; then
    if grep -q "unsatisfiable\|valid" "$TMPOUT"; then R="unsat"; else R="sat"; fi
    printf "%-4s %-8s %-10s\n" "$n" "$R" "${MS}"
  elif [ "$RC" -eq 124 ] || [ "$RC" -eq 143 ]; then
    printf "%-4s %-8s\n" "$n" "TIMEOUT"
  else
    printf "%-4s %-8s %-10s\n" "$n" "OOM" "${MS}"
  fi
  rm -f "$TMPOUT"
done
SCRIPT

RUN cat <<'SCRIPT' > /usr/local/bin/forall-experiment && chmod +x /usr/local/bin/forall-experiment
#!/bin/bash
set -euo pipefail
echo "forall on empty string experiment"
echo "================================="
echo ""
echo "MONA's M2L-STR requires nonempty strings. EREQ intersects"
echo "with (_+) to match. without (_+), the empty string can"
echo "vacuously satisfy forall."
echo ""
# EREQ results (with and without _+)
forall_empty_string
echo ""
# MONA results
echo "MONA results"
echo "------------"
printf "%-45s %s\n" "formula" "result"
for pair in \
  "all1 x: x < x|m2l-str; all1 x: x < x;" \
  "~(ex1 x: 0 <= x)|m2l-str; ~(ex1 x: 0 <= x);" \
  "all1 x: x < x & x < x|m2l-str; all1 x: (x < x & x < x);" \
  "var2 A; all1 x: x in A & x notin A|var2 A; all1 x: x in A & x notin A;" \
; do
  NAME="${pair%%|*}"
  FORMULA="${pair##*|}"
  TMPFILE=$(mktemp --suffix=.mona)
  echo "$FORMULA" > "$TMPFILE"
  TMPOUT=$(mktemp)
  mona-limited "$TMPFILE" > "$TMPOUT" 2>&1 && RC=0 || RC=$?
  if [ "$RC" -eq 0 ]; then
    if grep -q "unsatisfiable\|valid" "$TMPOUT"; then R="UNSAT"; else R="SAT"; fi
  else
    R="ERROR"
  fi
  printf "%-45s %s\n" "$NAME" "$R"
  rm -f "$TMPFILE" "$TMPOUT"
done
SCRIPT

RUN cat <<'SCRIPT' > /usr/local/bin/collect-random-times && chmod +x /usr/local/bin/collect-random-times
#!/bin/sh
# extract solved times (seconds) from results/benchmarks_random_*.md into JSON
# reads all result files that exist, so the plot accumulates as you run more levels
set -e
(
  for f in results/benchmarks_random_N*.md; do
    [ -f "$f" ] || continue
    # lines like: | P0.5N2L10.form0.mona | 4 | 5644 |
    awk -F'|' '/^\|.*\.mona/ && $3+0 > 0 { gsub(/ /,"",$3); print $3/1000 }' "$f"
  done
) | sort -n | jq -s '.' > plots/data/all_automatark_ereq.json
echo "collected $(jq length plots/data/all_automatark_ereq.json) solved times into plots/data/all_automatark_ereq.json"
SCRIPT

RUN cat <<'SCRIPT' > /usr/local/bin/gen-plots && chmod +x /usr/local/bin/gen-plots
#!/bin/sh
set -e
# collect fresh EREQ times from any result files that exist
collect-random-times 2>/dev/null || true
cd /ereq/plots
node gen-cactus.mjs
node gen-cactus.mjs --structured 2>/dev/null || echo "skipping structured plot (run run-ltlf.sh first)"
cp figs/*.pdf /ereq/results/ 2>/dev/null && echo "copied to results/" || true
SCRIPT

RUN cat <<'SCRIPT' > /usr/local/bin/run-random.sh && chmod +x /usr/local/bin/run-random.sh
#!/bin/sh
# quick random benchmark validation + plot generation.
# runs L10 (1000 formulas, ~2 minutes), then generates the cactus plot.
# the plot includes pre-recorded MONA data and all EREQ levels that have been run.
set -e
TIMEOUT="${1:-30}"
echo "=== random benchmark validation (L10, ${TIMEOUT}s timeout) ==="
echo ""
benchmarks-random "N2L10." "$TIMEOUT" --subprocess || true
echo ""
benchmarks-random "N4L10." "$TIMEOUT" --subprocess || true
echo ""
echo "=== generating cactus plot ==="
gen-plots
echo ""
echo "output: results/cactus-random.pdf"
echo "        results/cactus-structured.pdf"
SCRIPT

RUN cat <<'SCRIPT' > /usr/local/bin/distance-bench && chmod +x /usr/local/bin/distance-bench
#!/bin/sh
set -e
MAX_N="${1:-20}"
echo "=== EREQ distance (n=2..${MAX_N}) ==="
distance "$MAX_N"
echo ""
echo "=== MONA distance (n=2..${MAX_N}) ==="
mona-distance "$MAX_N"
SCRIPT

RUN cat <<'SCRIPT' > /usr/local/bin/config-experiment-sh && chmod +x /usr/local/bin/config-experiment-sh
#!/bin/sh
# demonstrates that no single config solves all hard cases.
# 3 representative cases x 3 configs, 2s timeout, <1 minute total.
T=2
CASES="data/random/P0.5N4L20.form128.mona data/random/P0.5N4L20.form319.mona data/random/P0.5N4L30.form1.mona"
CONFIGS="default dnf tf"

printf "%-30s" "formula"
for c in $CONFIGS; do printf " %10s" "$c"; done
echo ""
printf '%s\n' "$(printf '%.0s-' $(seq 1 62))"

for f in $CASES; do
  name=$(basename "$f")
  printf "%-30s" "$name"
  for c in $CONFIGS; do
    bin="config-experiment-$c"
    result=$(timeout --kill-after=2s "${T}s" sh -c "ulimit -v 2097152 2>/dev/null; exec $bin --run-single '$f'" 2>/dev/null) && rc=0 || rc=$?
    if [ $rc -eq 0 ] && echo "$result" | grep -q "^RESULT"; then
      ms=$(echo "$result" | grep "^RESULT" | awk '{print $2}')
      printf " %8sms" "$ms"
    else
      printf " %10s" "TO"
    fi
  done
  echo ""
done

echo ""
echo "dnf solves form128 but not form319."
echo "tf  solves form319 but not form128."
echo "no single configuration solves all cases."
SCRIPT

RUN cat <<'SCRIPT' > /usr/local/bin/gaston-bench && chmod +x /usr/local/bin/gaston-bench
#!/bin/sh
set -e
TIMEOUT="${1:-30}"
benchmarks_gaston "$TIMEOUT"
SCRIPT

RUN cat <<'MOTD' >> /etc/bash.bashrc

echo "EREQ benchmark container"
echo ""
echo "  run-ltlf.sh [--timeout 60]                   # structured: EREQ vs MONA + cactus plot (Figure 5)"
echo "  run-random.sh [timeout]                      # random: run L10 + generate cactus plot (Figure 4)"
echo "  distance-bench [max_n]                       # EREQ + MONA distance comparison (Table 3)"
echo ""
echo "  benchmarks lift                              # EREQ lift (included in run-ltlf.sh)"
echo "  benchmarks counter                           # EREQ counter (included in run-ltlf.sh)"
echo "  benchmarks-random \"N2L20.\" 30 --subprocess   # EREQ random benchmarks"
echo "  bench-all [start_level] [--long]             # all random L10-L100"
echo "  config-experiment-sh                         # configuration sensitivity (Section 8.2)"
echo "  forall-experiment                            # forall on empty string (EREQ + MONA)"
echo "  gaston-bench [timeout]                       # gaston WS1S benchmarks (comparison only)"
echo "  gen-plots                                    # regenerate cactus plots from results"
echo ""
echo "results are written to ./results/"
echo ""
MOTD

ENTRYPOINT []
CMD ["/bin/bash"]
