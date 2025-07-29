#!/bin/bash
# run from inside ./z3/build

Z3=./z3
OPTIONS="-v:0 -st smt.threads=4"
OUT_FILE="../z3_results.txt"
BASE_PATH="../../z3-poly-testing/inputs/"

# List of relative test files (relative to BASE_PATH)
REL_TEST_FILES=(
    "QF_NIA_small/Ton_Chanh_15__Singapore_v1_false-termination.c__p27381_terminationG_0.smt2"
    "QF_UFDTLIA_SAT/52759_bec3a2272267494faeecb6bfaf253e3b_10_QF_UFDTLIA.smt2"
)

# Clear output file
> "$OUT_FILE"

# Loop through and run Z3 on each file
for rel_path in "${REL_TEST_FILES[@]}"; do
    full_path="$BASE_PATH$rel_path"
    test_name="$rel_path"

    echo "Running: $test_name"
    echo "===== $test_name =====" | tee -a "$OUT_FILE"

    # Run Z3 and pipe output to both screen and file
    $Z3 "$full_path" $OPTIONS 2>&1 | tee -a "$OUT_FILE"

    echo "" | tee -a "$OUT_FILE"
done

echo "Results written to $OUT_FILE"
