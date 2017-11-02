# This script is intended to be included by other
# scripts and should not be executed directly

: ${Z3_SRC_DIR?"Z3_SRC_DIR must be specified"}
: ${ASAN_BUILD?"ASAN_BUILD must be specified"}
: ${UBSAN_BUILD?"UBSAN_BUILD must be specified"}

if [ "X${ASAN_BUILD}" = "X1" ]; then
  # Use suppression files
  export LSAN_OPTIONS="suppressions=${Z3_SRC_DIR}/contrib/suppressions/sanitizers/lsan.txt"
  # NOTE: If you get bad stacktraces try using `fast_unwind_on_malloc=0`
  # NOTE: `malloc_context_size` controls size of recorded stacktrace for allocations.
  #       If the reported stacktraces appear incomplete try increasing the value.
  export ASAN_OPTIONS="malloc_context_size=100,suppressions=${Z3_SRC_DIR}/contrib/suppressions/sanitizers/asan.txt"

  : ${SANITIZER_PRINT_SUPPRESSIONS?"SANITIZER_PRINT_SUPPRESSIONS must be specified"}
  if [ "X${SANITIZER_PRINT_SUPPRESSIONS}" = "X1" ]; then
    export LSAN_OPTIONS="${LSAN_OPTIONS},print_suppressions=1"
    export ASAN_OPTIONS="${ASAN_OPTIONS},print_suppressions=1"
  else
    export LSAN_OPTIONS="${LSAN_OPTIONS},print_suppressions=0"
    export ASAN_OPTIONS="${ASAN_OPTIONS},print_suppressions=0"
  fi

  : ${ASAN_SYMBOLIZER_PATH?"ASAN_SYMBOLIZER_PATH must be specified"}

  # Run command without checking for leaks
  function run_no_lsan() {
    ASAN_OPTIONS="${ASAN_OPTIONS},detect_leaks=0" "${@}"
  }

  # Check path to ASan DSO
  : ${ASAN_DSO?"ASAN_DSO must be specified"}
  if [ ! -e "${ASAN_DSO}" ]; then
    echo "ASAN_DSO (${ASAN_DSO}) does not exist"
    exit 1
  fi
  # FIXME: We'll need to refactor this when we can do UBSan builds
  # against a UBSan DSO.
  function run_non_native_binding() {
    # We need to preload the ASan DSO that libz3
    # will have undefined references to.
    # Don't run leak checking because we get lots reported leaks
    # in the language runtime (e.g. python).
    PLATFORM="$(uname -s)"
    case "${PLATFORM}" in
      Linux*)
        LD_PRELOAD="${ASAN_DSO}" run_no_lsan "${@}"
      ;;
      Darwin*)
        DYLD_INSERT_LIBRARIES="${ASAN_DSO}" run_no_lsan "${@}"
      ;;
      *)
        echo "Unknown platform \"${PLATFORM}\""
        exit 1
      ;;
    esac
    unset PLATFORM
  }
else
  # In non-ASan build just run directly
  function run_no_lsan() {
    "${@}"
  }
  function run_non_native_binding() {
    "${@}"
  }
fi

if [ "X${UBSAN_BUILD}" = "X1" ]; then
  # `halt_on_error=1,abort_on_error=1` means that on the first UBSan error
  # the program will terminate by calling `abort(). Without this UBSan will
  # allow execution to continue. We also use a suppression file.
  export UBSAN_OPTIONS="halt_on_error=1,abort_on_error=1,suppressions=${Z3_SRC_DIR}/contrib/suppressions/sanitizers/ubsan.txt"

  : ${SANITIZER_PRINT_SUPPRESSIONS?"SANITIZER_PRINT_SUPPRESSIONS must be specified"}
  if [ "X${SANITIZER_PRINT_SUPPRESSIONS}" = "X1" ]; then
    export UBSAN_OPTIONS="${UBSAN_OPTIONS},print_suppressions=1"
  else
    export UBSAN_OPTIONS="${UBSAN_OPTIONS},print_suppressions=0"
  fi
fi
