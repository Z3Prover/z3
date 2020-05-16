#!/bin/bash
# This script builds Z3

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"

set -x
set -e
set -o pipefail

: ${Z3_SRC_DIR?"Z3_SRC_DIR must be specified"}
: ${Z3_BUILD_DIR?"Z3_BUILD_DIR must be specified"}
: ${Z3_BUILD_TYPE?"Z3_BUILD_TYPE must be specified"}
: ${Z3_CMAKE_GENERATOR?"Z3_CMAKE_GENERATOR must be specified"}
: ${Z3_STATIC_BUILD?"Z3_STATIC_BUILD must be specified"}
: ${Z3_USE_LIBGMP?"Z3_USE_LIBGMP must be specified"}
: ${BUILD_DOCS?"BUILD_DOCS must be specified"}
: ${PYTHON_EXECUTABLE?"PYTHON_EXECUTABLE must be specified"}
: ${PYTHON_BINDINGS?"PYTHON_BINDINGS must be specified"}
: ${DOTNET_BINDINGS?"DOTNET_BINDINGS must be specified"}
: ${JAVA_BINDINGS?"JAVA_BINDINGS must be specified"}
: ${USE_LTO?"USE_LTO must be specified"}
: ${Z3_INSTALL_PREFIX?"Z3_INSTALL_PREFIX must be specified"}
: ${Z3_WARNINGS_AS_ERRORS?"Z3_WARNINGS_AS_ERRORS must be specified"}
: ${UBSAN_BUILD?"UBSAN_BUILD must be specified"}

ADDITIONAL_Z3_OPTS=()

# Static or dynamic libz3
if [ "X${Z3_STATIC_BUILD}" = "X1" ]; then
  ADDITIONAL_Z3_OPTS+=('-DZ3_BUILD_LIBZ3_SHARED=OFF')
else
  ADDITIONAL_Z3_OPTS+=('-DZ3_BUILD_LIBZ3_SHARED=ON')
fi

# Use LibGMP?
if [ "X${Z3_USE_LIBGMP}" = "X1" ]; then
  ADDITIONAL_Z3_OPTS+=('-DZ3_USE_LIB_GMP=ON')
else
  ADDITIONAL_Z3_OPTS+=('-DZ3_USE_LIB_GMP=OFF')
fi

# Use link time optimziation?
if [ "X${USE_LTO}" = "X1" ]; then
  ADDITIONAL_Z3_OPTS+=('-DZ3_LINK_TIME_OPTIMIZATION=ON')
else
  ADDITIONAL_Z3_OPTS+=('-DZ3_LINK_TIME_OPTIMIZATION=OFF')
fi

# Build API docs?
if [ "X${BUILD_DOCS}" = "X1" ]; then
  ADDITIONAL_Z3_OPTS+=( \
    '-DZ3_BUILD_DOCUMENTATION=ON' \
    '-DZ3_ALWAYS_BUILD_DOCS=OFF' \
  )
else
  ADDITIONAL_Z3_OPTS+=('-DZ3_BUILD_DOCUMENTATION=OFF')
fi

# Python bindings?
if [ "X${PYTHON_BINDINGS}" = "X1" ]; then
  ADDITIONAL_Z3_OPTS+=( \
    '-DZ3_BUILD_PYTHON_BINDINGS=ON' \
    '-DZ3_INSTALL_PYTHON_BINDINGS=ON' \
  )
else
  ADDITIONAL_Z3_OPTS+=( \
    '-DZ3_BUILD_PYTHON_BINDINGS=OFF' \
    '-DZ3_INSTALL_PYTHON_BINDINGS=OFF' \
  )
fi

# .NET bindings?
if [ "X${DOTNET_BINDINGS}" = "X1" ]; then
  ADDITIONAL_Z3_OPTS+=( \
    '-DZ3_BUILD_DOTNET_BINDINGS=ON' \
    '-DZ3_INSTALL_DOTNET_BINDINGS=ON' \
  )
else
  ADDITIONAL_Z3_OPTS+=( \
    '-DZ3_BUILD_DOTNET_BINDINGS=OFF' \
    '-DZ3_INSTALL_DOTNET_BINDINGS=OFF' \
  )
fi

# Java bindings?
if [ "X${JAVA_BINDINGS}" = "X1" ]; then
  ADDITIONAL_Z3_OPTS+=( \
    '-DZ3_BUILD_JAVA_BINDINGS=ON' \
    '-DZ3_INSTALL_JAVA_BINDINGS=ON' \
  )
else
  ADDITIONAL_Z3_OPTS+=( \
    '-DZ3_BUILD_JAVA_BINDINGS=OFF' \
    '-DZ3_INSTALL_JAVA_BINDINGS=OFF' \
  )
fi

# Set compiler flags
source ${SCRIPT_DIR}/set_compiler_flags.sh

if [ "X${UBSAN_BUILD}" = "X1" ]; then
  # HACK: When building with UBSan the C++ linker
  # must be used to avoid the following linker errors.
  # undefined reference to `__ubsan_vptr_type_cache'
  # undefined reference to `__ubsan_handle_dynamic_type_cache_miss'
  ADDITIONAL_Z3_OPTS+=( \
    '-DZ3_C_EXAMPLES_FORCE_CXX_LINKER=ON' \
  )
fi

# Sanity check
if [ ! -e "${Z3_SRC_DIR}/CMakeLists.txt" ]; then
  echo "Z3_SRC_DIR is invalid"
  exit 1
fi

# Make build tree
mkdir -p "${Z3_BUILD_DIR}"
cd "${Z3_BUILD_DIR}"

# Configure
cmake \
  -G "${Z3_CMAKE_GENERATOR}" \
  -DCMAKE_BUILD_TYPE=${Z3_BUILD_TYPE} \
  -DPYTHON_EXECUTABLE=${PYTHON_EXECUTABLE} \
  -DCMAKE_INSTALL_PREFIX=${Z3_INSTALL_PREFIX} \
  -DWARNINGS_AS_ERRORS=${Z3_WARNINGS_AS_ERRORS} \
  "${ADDITIONAL_Z3_OPTS[@]}" \
  "${Z3_SRC_DIR}"

# Build
source ${SCRIPT_DIR}/set_generator_args.sh
cmake --build $(pwd) "${GENERATOR_ARGS[@]}"
