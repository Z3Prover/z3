#!/bin/bash

set -x
set -e
set -o pipefail

: ${Z3_BUILD_DIR?"Z3_BUILD_DIR must be specified"}
: ${Z3_BUILD_TYPE?"Z3_BUILD_TYPE must be specified"}
: ${RUN_SYSTEM_TESTS?"RUN_SYSTEM_TESTS must be speicifed"}
: ${PYTHON_BINDINGS?"PYTHON_BINDINGS must be specified"}
: ${PYTHON_EXECUTABLE?"PYTHON_EXECUTABLE must be specified"}
: ${Z3_SYSTEM_TEST_DIR?"Z3_SYSTEM_TEST_DIR must be specified"}
: ${UBSAN_BUILD?"UBSAN_BUILD must be specified"}

if [ "X${RUN_SYSTEM_TESTS}" != "X1" ]; then
  echo "Skipping system tests"
  exit 0
fi

# Sanitizer environment variables
SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"
source ${SCRIPT_DIR}/sanitizer_env.sh

Z3_EXE="${Z3_BUILD_DIR}/z3"
Z3_LIB_DIR="${Z3_BUILD_DIR}"

# Set value if not already defined externally
Z3_SYSTEM_TEST_GIT_URL="${Z3_GIT_URL:-https://github.com/Z3Prover/z3test.git}"

# Clone repo to destination
mkdir -p "${Z3_SYSTEM_TEST_DIR}"
git clone "${Z3_SYSTEM_TEST_GIT_URL}" "${Z3_SYSTEM_TEST_DIR}"
cd "${Z3_SYSTEM_TEST_DIR}"

if [ -n "${Z3_SYSTEM_TEST_GIT_REVISION}" ]; then
  # If a particular revision is requested then check it out.
  # This is useful for reproducible builds
  git checkout "${Z3_SYSTEM_TEST_GIT_REVISION}"
fi

###############################################################################
# Run system tests
###############################################################################

# SMTLIBv2 tests
${PYTHON_EXECUTABLE} scripts/test_benchmarks.py "${Z3_EXE}" regressions/smt2

${PYTHON_EXECUTABLE} scripts/test_benchmarks.py "${Z3_EXE}" regressions/smt2-extra

if [ "X${Z3_BUILD_TYPE}" = "XDebug" ]; then
  ${PYTHON_EXECUTABLE} scripts/test_benchmarks.py "${Z3_EXE}" regressions/smt2-debug
fi

if [ "X${PYTHON_BINDINGS}" = "X1" ]; then
  # Run python binding tests
  if [ "X${UBSAN_BUILD}" = "X1" ]; then
    # FIXME: We need to build libz3 with a shared UBSan runtime for the bindings
    # to work.
    echo "FIXME: Skipping python binding tests when building with UBSan"
  elif [ "X${ASAN_BUILD}" = "X1" ]; then
    # FIXME: The `test_pyscripts.py` doesn't propagate LD_PRELOAD
    # so under ASan the tests fail to run
    # to work.
    echo "FIXME: Skipping python binding tests when building with ASan"
  else
    run_non_native_binding ${PYTHON_EXECUTABLE} scripts/test_pyscripts.py "${Z3_LIB_DIR}" regressions/python/
  fi
fi

# FIXME: Run `scripts/test_cs.py` once it has been modified to support mono
