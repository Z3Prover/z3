#!/bin/bash

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"
. ${SCRIPT_DIR}/run_quiet.sh

set -x
set -e
set -o pipefail

: ${Z3_BUILD_DIR?"Z3_BUILD_DIR must be specified"}
: ${RUN_UNIT_TESTS?"RUN_UNIT_TESTS must be specified"}

if [ "X${RUN_UNIT_TESTS}" != "X1" ]; then
  echo "Skipping unit tests"
  exit 0
fi

# Set CMake generator args
source ${SCRIPT_DIR}/set_generator_args.sh

cd "${Z3_BUILD_DIR}"

# Build and run internal tests
cmake --build $(pwd) --target test-z3 "${GENERATOR_ARGS[@]}"
# Run all tests that don't require arguments
run_quiet ./test-z3 /a
