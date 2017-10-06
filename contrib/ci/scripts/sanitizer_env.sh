# This script is intended to be included by other
# scripts and should not be executed directly

: ${Z3_SRC_DIR?"Z3_SRC_DIR must be specified"}
: ${ASAN_BUILD?"ASAN_BUILD must be specified"}
: ${UBSAN_BUILD?"UBSAN_BUILD must be specified"}

if [ "X${ASAN_BUILD}" = "X1" ]; then
  # Use suppression files
  export LSAN_OPTIONS="print_suppressions=1,suppressions=${Z3_SRC_DIR}/contrib/suppressions/sanitizers/lsan.txt"
  export ASAN_OPTIONS="print_suppressions=1,suppressions=${Z3_SRC_DIR}/contrib/suppressions/sanitizers/asan.txt"
fi

if [ "X${UBSAN_BUILD}" = "X1" ]; then
  # `halt_on_error=1,abort_on_error=1` means that on the first UBSan error
  # the program will terminate by calling `abort(). Without this UBSan will
  # allow execution to continue. We also use a suppression file.
  export UBSAN_OPTIONS="halt_on_error=1,abort_on_error=1,print_suppressions=1,suppressions=${Z3_SRC_DIR}/contrib/suppressions/sanitizers/ubsan.txt"
fi
