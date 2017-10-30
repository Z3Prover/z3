#!/bin/bash

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"
. ${SCRIPT_DIR}/run_quiet.sh

set -x
set -e
set -o pipefail

: ${Z3_BUILD_DIR?"Z3_BUILD_DIR must be specified"}
: ${RUN_UNIT_TESTS?"RUN_UNIT_TESTS must be specified"}

# Set CMake generator args
source ${SCRIPT_DIR}/set_generator_args.sh

# Sanitizer environment variables
source ${SCRIPT_DIR}/sanitizer_env.sh

cd "${Z3_BUILD_DIR}"

function build_unit_tests() {
  # Build internal tests
  cmake --build $(pwd) --target test-z3 "${GENERATOR_ARGS[@]}"
}

function run_unit_tests() {
  # Run all tests that don't require arguments
  run_quiet ./test-z3 /a
}

case "${RUN_UNIT_TESTS}" in
  BUILD_AND_RUN)
    build_unit_tests
    run_unit_tests
  ;;
  BUILD_ONLY)
    build_unit_tests
  ;;
  SKIP)
    echo "RUN_UNIT_TESTS set to \"${RUN_UNIT_TESTS}\" so skipping build and run"
    exit 0
  ;;
  *)
    echo "Error: RUN_UNIT_TESTS set to unhandled value \"${RUN_UNIT_TESTS}\""
    exit 1
  ;;
esac
