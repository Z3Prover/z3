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

if [ "X${RUN_SYSTEM_TESTS}" != "X1" ]; then
  echo "Skipping system tests"
  exit 0
fi

Z3_EXE="${Z3_BUILD_DIR}/z3"
Z3_LIB_DIR="${Z3_BUILD_DIR}"

# Set value if not already defined externally
Z3_SYSTEM_TEST_GIT_URL="${Z3_GIT_URL:-https://github.com/Z3Prover/z3test.git}"

# Clone repo to destination
mkdir -p "${Z3_SYSTEM_TEST_GIT_URL}"
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
  ${PYTHON_EXECUTABLE} scripts/test_pyscripts.py "${Z3_LIB_DIR}" regressions/python/
fi

# FIXME: Run `scripts/test_cs.py` once it has been modified to support mono
