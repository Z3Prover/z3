#!/usr/bin/env bash
set -euo pipefail

# --- Inputs ---
FILE=$(realpath "$1")
Z3=$(realpath "$2")
N="${3:-99999999}"   # optional limit on number of tests

TIMEOUT=100
OUT="../sweep_results.csv"

echo "id,params,result,time_s" > "$OUT"

# --- Tunable parameters ---
BOOL_PARAMS=(
  "smt.arith.nl.branching"
  "smt.arith.nl.cross_nested"
  "smt.arith.nl.expensive_patching"
  "smt.arith.nl.gb"
  "smt.arith.nl.horner"
  "smt.arith.nl.optimize_bounds"
  "smt.arith.nl.propagate_linear_monomials"
  "smt.arith.nl.tangents"
)

INT_PARAM1_KEY="smt.arith.nl.delay"
INT_PARAM1_LO=5
INT_PARAM1_HI=10

INT_PARAM2_KEY="smt.arith.nl.horner_frequency"
INT_PARAM2_LO=2
INT_PARAM2_HI=6

id=1

# --- Deterministic nested loops over all parameter values ---
for b0 in 0 1; do
for b1 in 0 1; do
for b2 in 0 1; do
for b3 in 0 1; do
for b4 in 0 1; do
for b5 in 0 1; do
for b6 in 0 1; do
for b7 in 0 1; do

  for d in $(seq "$INT_PARAM1_LO" "$INT_PARAM1_HI"); do
  for hf in $(seq "$INT_PARAM2_LO" "$INT_PARAM2_HI"); do

    # stop early if N reached
    if (( id > N )); then
        echo "✓ Done early at $((id-1)) combinations. Results in $OUT"
        exit 0
    fi

    BOOLS=($b0 $b1 $b2 $b3 $b4 $b5 $b6 $b7)

    PARAMS=()
    for idx in "${!BOOL_PARAMS[@]}"; do
        PARAMS+=("${BOOL_PARAMS[$idx]}=${BOOLS[$idx]}")
    done
    PARAMS+=("$INT_PARAM1_KEY=$d")
    PARAMS+=("$INT_PARAM2_KEY=$hf")

    PARAM_STR=$(IFS=, ; echo "${PARAMS[*]}")

    printf "[%05d] %s\n" "$id" "$PARAM_STR"

    # ----- Run Z3 -----
    START=$(date +%s%N)
    if timeout "$TIMEOUT" "$Z3" \
        -v:1 -st \
        "$FILE" \
        smt.threads=2 \
        tactic.default_tactic=smt \
        smt_parallel.param_tuning=false \
        smt_parallel.tunable_params="$PARAM_STR" \
        >/tmp/z3_out.txt 2>&1
    then
        RESULT=$(grep -E "sat|unsat|unknown" /tmp/z3_out.txt | tail -1)
        [[ -z "$RESULT" ]] && RESULT="unknown"
    else
        RESULT="timeout"
    fi
    END=$(date +%s%N)
    TIME=$(awk "BEGIN{print ($END-$START)/1e9}")

    echo "$id,\"$PARAM_STR\",$RESULT,$TIME" >> "$OUT"

    ((id++))

  done # hf
  done # d

done; done; done; done; done; done; done; done
