#!/bin/bash

# This script tests Z3

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"
. ${SCRIPT_DIR}/run_quiet.sh

set -x
set -e
set -o pipefail
: ${Z3_SRC_DIR?"Z3_SRC_DIR must be specified"}
: ${Z3_BUILD_DIR?"Z3_BUILD_DIR must be specified"}
: ${PYTHON_BINDINGS?"PYTHON_BINDINGS must be specified"}
: ${PYTHON_EXECUTABLE?"PYTHON_EXECUTABLE must be specified"}
: ${DOTNET_BINDINGS?"DOTNET_BINDINGS must be specified"}
: ${JAVA_BINDINGS?"JAVA_BINDINGS must be specified"}
: ${UBSAN_BUILD?"UBSAN_BUILD must be specified"}
: ${RUN_API_EXAMPLES?"RUN_API_EXAMPLES must be specified"}

if [ "X${RUN_API_EXAMPLES}" = "X0" ]; then
  echo "Skipping run of API examples"
  exit 0
fi

# Set compiler flags
source ${SCRIPT_DIR}/set_compiler_flags.sh

# Set CMake generator args
source ${SCRIPT_DIR}/set_generator_args.sh

# Sanitizer environment variables
source ${SCRIPT_DIR}/sanitizer_env.sh

cd "${Z3_BUILD_DIR}"

# Build and run C example
cmake --build $(pwd) --target c_example "${GENERATOR_ARGS[@]}"
run_quiet examples/c_example_build_dir/c_example

# Build and run C++ example
cmake --build $(pwd) --target cpp_example "${GENERATOR_ARGS[@]}"
run_quiet examples/cpp_example_build_dir/cpp_example

# Build and run tptp5 example
cmake --build $(pwd) --target z3_tptp5 "${GENERATOR_ARGS[@]}"
# FIXME: Do something more useful with example
run_quiet examples/tptp_build_dir/z3_tptp5 -help

# Build an run c_maxsat_example
cmake --build $(pwd) --target c_maxsat_example "${GENERATOR_ARGS[@]}"
# FIXME: It is known that the maxsat example leaks memory and the
# the Z3 developers have stated this is "wontfix".
# See https://github.com/Z3Prover/z3/issues/1299
run_no_lsan \
  run_quiet \
    examples/c_maxsat_example_build_dir/c_maxsat_example \
    ${Z3_SRC_DIR}/examples/maxsat/ex.smt

if [ "X${UBSAN_BUILD}" = "X1" ]; then
  # FIXME: We really need libz3 to link against a shared UBSan runtime.
  # Right now we link against the static runtime which breaks all the
  # non-native language bindings.
  echo "FIXME: Can't run other examples when building with UBSan"
  exit 0
fi


if [ "X${PYTHON_BINDINGS}" = "X1" ]; then
  # Run python examples
  # `all_interval_series.py` produces a lot of output so just throw
  # away output.
  # TODO: This example is slow should we remove it from testing?
  if [ "X${ASAN_BUILD}" = "X1" -a "X${Z3_BUILD_TYPE}" = "XDebug" ]; then
    # Too slow when doing ASan Debug build
    echo "Skipping all_interval_series.py under ASan Debug build"
  else
    run_quiet run_non_native_binding ${PYTHON_EXECUTABLE} python/all_interval_series.py
  fi
  run_quiet run_non_native_binding ${PYTHON_EXECUTABLE} python/complex.py
  run_quiet run_non_native_binding ${PYTHON_EXECUTABLE} python/example.py
  # FIXME: `hamiltonian.py` example is disabled because its too slow.
  #${PYTHON_EXECUTABLE} python/hamiltonian.py
  run_quiet run_non_native_binding ${PYTHON_EXECUTABLE} python/marco.py
  run_quiet run_non_native_binding ${PYTHON_EXECUTABLE} python/mss.py
  run_quiet run_non_native_binding ${PYTHON_EXECUTABLE} python/socrates.py
  run_quiet run_non_native_binding ${PYTHON_EXECUTABLE} python/visitor.py
  run_quiet run_non_native_binding ${PYTHON_EXECUTABLE} python/z3test.py
fi

if [ "X${DOTNET_BINDINGS}" = "X1" ]; then
  # Build .NET example
  # FIXME: Move compliation step into CMake target
  mcs ${Z3_SRC_DIR}/examples/dotnet/Program.cs /target:exe /out:dotnet_test.exe /reference:Microsoft.Z3.dll /r:System.Numerics.dll
  # Run .NET example
  run_quiet run_non_native_binding mono ./dotnet_test.exe
fi

if [ "X${JAVA_BINDINGS}" = "X1" ]; then
  # Build Java example
  # FIXME: Move compilation step into CMake target
  mkdir -p examples/java
  cp ${Z3_SRC_DIR}/examples/java/JavaExample.java examples/java/
  javac examples/java/JavaExample.java -classpath com.microsoft.z3.jar
  # Run Java example
  if [ "$(uname)" = "Darwin" ]; then
    # macOS
    export DYLD_LIBRARY_PATH=$(pwd):${DYLD_LIBRARY_PATH}
  else
    # Assume Linux for now
    export LD_LIBRARY_PATH=$(pwd):${LD_LIBRARY_PATH}
  fi
  if [ "X${ASAN_BUILD}" = "X1" ]; then
    # The JVM seems to crash (SEGV) if we pre-load ASan
    # so don't run it for now.
    echo "Skipping JavaExample under ASan build"
  else
    run_quiet \
      run_non_native_binding \
        java -cp .:examples/java:com.microsoft.z3.jar JavaExample
  fi
fi

