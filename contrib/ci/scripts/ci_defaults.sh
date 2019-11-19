# This file should be sourced by other scripts
# and not executed directly

# Set CI build defaults

export ASAN_BUILD="${ASAN_BUILD:-0}"
export BUILD_DOCS="${BUILD_DOCS:-0}"
export DOTNET_BINDINGS="${DOTNET_BINDINGS:-1}"
export JAVA_BINDINGS="${JAVA_BINDINGS:-1}"
export NO_SUPPRESS_OUTPUT="${NO_SUPPRESS_OUTPUT:-0}"
export PYTHON_BINDINGS="${PYTHON_BINDINGS:-1}"
export RUN_API_EXAMPLES="${RUN_API_EXAMPLES:-1}"
export RUN_SYSTEM_TESTS="${RUN_SYSTEM_TESTS:-1}"
export RUN_UNIT_TESTS="${RUN_UNIT_TESTS:-BUILD_AND_RUN}"
# Don't print suppressions by default because that breaks the Z3
# regression tests because they don't expect them to appear in Z3's
# output.
export SANITIZER_PRINT_SUPPRESSIONS="${SANITIZER_PRINT_SUPPRESSIONS:-0}"
export TARGET_ARCH="${TARGET_ARCH:-x86_64}"
export TEST_INSTALL="${TEST_INSTALL:-1}"
export UBSAN_BUILD="${UBSAN_BUILD:-0}"
export Z3_USE_LIBGMP="${Z3_USE_LIBGMP:-0}"
export USE_LTO="${USE_LTO:-0}"

export Z3_BUILD_TYPE="${Z3_BUILD_TYPE:-RelWithDebInfo}"
export Z3_CMAKE_GENERATOR="${Z3_CMAKE_GENERATOR:-Ninja}"
export Z3_STATIC_BUILD="${Z3_STATIC_BUILD:-0}"
# Default is blank which means get latest revision
export Z3_SYSTEM_TEST_GIT_REVISION="${Z3_SYSTEM_TEST_GIT_REVISION:-}"
export Z3_WARNINGS_AS_ERRORS="${Z3_WARNINGS_AS_ERRORS:-SERIOUS_ONLY}"
export Z3_VERBOSE_BUILD_OUTPUT="${Z3_VERBOSE_BUILD_OUTPUT:-0}"

# Platform specific defaults
PLATFORM="$(uname -s)"
case "${PLATFORM}" in
  Linux*)
    export C_COMPILER="${C_COMPILER:-gcc}"
    export CXX_COMPILER="${CXX_COMPILER:-g++}"
    export Z3_INSTALL_PREFIX="${Z3_INSTALL_PREFIX:-/usr}"
  ;;
  Darwin*)
    export C_COMPILER="${C_COMPILER:-clang}"
    export CXX_COMPILER="${CXX_COMPILER:-clang++}"
    export Z3_INSTALL_PREFIX="${Z3_INSTALL_PREFIX:-/usr/local}"
  ;;
  *)
    echo "Unknown platform \"${PLATFORM}\""
    exit 1
  ;;
esac
unset PLATFORM

# NOTE: The following variables are not set here because
# they are specific to the CI implementation
# PYTHON_EXECUTABLE
# ASAN_DSO
# Z3_SRC_DIR
# Z3_BUILD_DIR
# Z3_SYSTEM_TEST_DIR
