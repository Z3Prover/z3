#!/usr/bin/env bash
set -euo pipefail

# --- Inputs ---
FILE=$(realpath "$1")
Z3=$(realpath "$2")
N="${3:-2}"

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

INT_PARAMS=(
  "smt.arith.nl.delay:5:10"
  "smt.arith.nl.horner_frequency:2:6"
)

# --- Helpers ---
random_bool() { echo $((RANDOM % 2)); }

random_int() {
  local lo=$1
  local hi=$2
  echo $((lo + RANDOM % (hi - lo + 1)))
}

# --- Track used parameter combinations ---
declare -A SEEN

i=1
while (( i <= N )); do

    # ----- generate a unique parameter string -----
    while true; do
        PARAMS=()

        for p in "${BOOL_PARAMS[@]}"; do
            PARAMS+=("$p=$(random_bool)")
        done

        for spec in "${INT_PARAMS[@]}"; do
            IFS=':' read -r key lo hi <<<"$spec"
            PARAMS+=("$key=$(random_int "$lo" "$hi")")
        done

        PARAM_STR=$(IFS=, ; echo "${PARAMS[*]}")

        # Check uniqueness
        if [[ -z "${SEEN[$PARAM_STR]+x}" ]]; then
            SEEN["$PARAM_STR"]=1
            break
        fi
    done

    printf "[%03d/%03d] %s\n" "$i" "$N" "$PARAM_STR"

    # ----- run Z3 -----
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

    echo "$i,\"$PARAM_STR\",$RESULT,$TIME" >> "$OUT"

    ((i++))
done

echo "✓ Done. Results written to $OUT"
