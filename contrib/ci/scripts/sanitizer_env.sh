# This script is intended to be included by other
# scripts and should not be executed directly

: ${Z3_SRC_DIR?"Z3_SRC_DIR must be specified"}
: ${ASAN_BUILD?"ASAN_BUILD must be specified"}
: ${UBSAN_BUILD?"UBSAN_BUILD must be specified"}

if [ "X${ASAN_BUILD}" = "X1" ]; then
  # Use suppression files
  export LSAN_OPTIONS="print_suppressions=1,suppressions=${Z3_SRC_DIR}/contrib/suppressions/sanitizers/lsan.txt"
  # NOTE: If you get bad stacktraces try using `fast_unwind_on_malloc=0`
  # NOTE: `malloc_context_size` controls size of recorded stacktrace for allocations.
  #       If the reported stacktraces appear incomplete try increasing the value.
  export ASAN_OPTIONS="malloc_context_size=100,print_suppressions=1,suppressions=${Z3_SRC_DIR}/contrib/suppressions/sanitizers/asan.txt"
  : ${ASAN_SYMBOLIZER_PATH?"ASAN_SYMBOLIZER_PATH must be specified"}

  # Run command without checking for leaks
  function run_no_lsan() {
    ASAN_OPTIONS="${ASAN_OPTIONS},detect_leaks=0" "${@}"
  }
else
  # In non-ASan build just run directly
  function run_no_lsan() {
    "${@}"
  }
fi

if [ "X${UBSAN_BUILD}" = "X1" ]; then
  # `halt_on_error=1,abort_on_error=1` means that on the first UBSan error
  # the program will terminate by calling `abort(). Without this UBSan will
  # allow execution to continue. We also use a suppression file.
  export UBSAN_OPTIONS="halt_on_error=1,abort_on_error=1,print_suppressions=1,suppressions=${Z3_SRC_DIR}/contrib/suppressions/sanitizers/ubsan.txt"
fi
