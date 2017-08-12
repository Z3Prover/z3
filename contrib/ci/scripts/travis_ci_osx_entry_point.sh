#!/bin/bash

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"

set -x
set -e
set -o pipefail

# Set defaults
# FIXME: Refactor this so we don't need to stay in sync with
# `z3_build.Dockerfile`.
export ASAN_BUILD="${ASAN_BUILD:-0}"
export BUILD_DOCS="${BUILD_DOCS:-0}"
export C_COMPILER="${C_COMPILER:-clang}"
export CXX_COMPILER="${CXX_COMPILER:-clang++}"
export DOTNET_BINDINGS="${DOTNET_BINDINGS:-1}"
export JAVA_BINDINGS="${JAVA_BINDINGS:-1}"
export NO_SUPPRESS_OUTPUT="${NO_SUPPRESS_OUTPUT:-0}"
export PYTHON_BINDINGS="${PYTHON_BINDINGS:-1}"
export PYTHON_EXECUTABLE="$(which python)"
export RUN_SYSTEM_TESTS="${RUN_SYSTEM_TESTS:-1}"
export RUN_UNIT_TESTS="${RUN_UNIT_TESTS:-1}"
export TARGET_ARCH="${TARGET_ARCH:-x86_64}"
export TEST_INSTALL="${TEST_INSTALL:-1}"
export UBSAN_BUILD="${UBSAN_BUILD:-0}"
export USE_LIBGMP="${USE_LIBGMP:-0}"
export USE_LTO="${USE_LTO:-0}"
export USE_OPENMP="${USE_OPENMP:-1}"

if [ -z "${TRAVIS_BUILD_DIR}" ]; then
  echo "TRAVIS_BUILD_DIR must be set to root of Z3 repository"
  exit 1
fi

if [ ! -d "${TRAVIS_BUILD_DIR}" ]; then
  echo "TRAVIS_BUILD_DIR must be a directory"
  exit 1
fi

export Z3_SRC_DIR="${TRAVIS_BUILD_DIR}"
export Z3_BUILD_DIR="${Z3_SRC_DIR}/build"
export Z3_BUILD_TYPE="${Z3_BUILD_TYPE:-RelWithDebInfo}"
export Z3_CMAKE_GENERATOR="${Z3_CMAKE_GENERATOR:-Ninja}"
export Z3_INSTALL_PREFIX="${Z3_INSTALL_PREFIX:-/usr/local}"
export Z3_STATIC_BUILD="${Z3_STATIC_BUILD:-0}"
export Z3_SYSTEM_TEST_DIR="${Z3_SRC_DIR}/z3_system_test"
export Z3_WARNINGS_AS_ERRORS="${Z3_WARNINGS_AS_ERRORS:-SERIOUS_ONLY}"
export Z3_VERBOSE_BUILD_OUTPUT="${Z3_VERBOSE_BUILD_OUTPUT:-0}"

# Overwrite whatever what set in TravisCI
export CC="${C_COMPILER}"
export CXX="${CXX_COMPILER}"

if [ "X${MACOS_SKIP_DEPS_UPDATE}" = "X1" ]; then
  # This is just for local testing to avoid updating
  echo "Skipping dependency update"
else
  "${SCRIPT_DIR}/install_deps_osx.sh"
fi

# Build Z3
"${SCRIPT_DIR}/build_z3_cmake.sh"
# Test building docs
"${SCRIPT_DIR}/test_z3_docs.sh"
# Test examples
"${SCRIPT_DIR}/test_z3_examples_cmake.sh"
# Run unit tests
"${SCRIPT_DIR}/test_z3_unit_tests_cmake.sh"
# Run system tests
"${SCRIPT_DIR}/test_z3_system_tests.sh"
# Test install
"${SCRIPT_DIR}/test_z3_install_cmake.sh"
