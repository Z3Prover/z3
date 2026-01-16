#!/usr/bin/env bash

Z3=./build/z3
BENCH=../bench/inputs/QF_LIA/n8115-prp-14-33.smt2
RUNS=200
THREADS=4

OUTDIR=logs_n8115
mkdir -p "$OUTDIR"

for i in $(seq 1 $RUNS); do
  SEED=$RANDOM
  LOG="$OUTDIR/run_$i.seed_$SEED.log"

  echo "=== RUN $i (seed=$SEED) ===" | tee "$LOG"

  $Z3 "$BENCH" \
    -v:1 -st \
    smt.threads=$THREADS \
    smt.random_seed=$SEED \
    tactic.default_tactic=smt \
    smt_parallel.inprocessing=false \
    smt.auto_config=false \
    > "$LOG" 2>&1

  RESULT=$(grep -E "^(sat|unsat|unknown)$" "$LOG" | tail -n 1)

  if [[ "$RESULT" == "unknown" ]]; then
    echo "🔥 UNKNOWN FOUND (seed=$SEED) → $LOG"
  fi
done
