#!/bin/bash

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"

set -x
set -e
set -o pipefail

# Get defaults
source "${SCRIPT_DIR}/ci_defaults.sh"

if [ -z "${TRAVIS_BUILD_DIR}" ]; then
  echo "TRAVIS_BUILD_DIR must be set to root of Z3 repository"
  exit 1
fi

if [ ! -d "${TRAVIS_BUILD_DIR}" ]; then
  echo "TRAVIS_BUILD_DIR must be a directory"
  exit 1
fi

# These variables are specific to the macOS TravisCI
# implementation and are not set in `ci_defaults.sh`.
export PYTHON_EXECUTABLE="${PYTHON_EXECUTABLE:-$(which python)}"
export Z3_SRC_DIR="${TRAVIS_BUILD_DIR}"
export Z3_BUILD_DIR="${Z3_SRC_DIR}/build"
export Z3_SYSTEM_TEST_DIR="${Z3_SRC_DIR}/z3_system_test"

if [ "X${MACOS_SKIP_DEPS_UPDATE}" = "X1" ]; then
  # This is just for local testing to avoid updating
  echo "Skipping dependency update"
else
  "${SCRIPT_DIR}/install_deps_osx.sh"
fi

# Build Z3
if [ "${USE_OPENMP}" = 1 ]; then
   "${TRAVIS_BUILD_DIR}/package_z3_osx_openmp.sh"
else
   "${TRAVIS_BUILD_DIR}/package_z3_osx.sh"
fi

