# This script is intended to be included by other
# scripts and should not be executed directly

: ${Z3_CMAKE_GENERATOR?"Z3_CMAKE_GENERATOR must be specified"}
: ${Z3_VERBOSE_BUILD_OUTPUT?"Z3_VERBOSE_BUILD_OUTPUT must be specified"}

GENERATOR_ARGS=('--')
if [ "${Z3_CMAKE_GENERATOR}" = "Unix Makefiles" ]; then
  GENERATOR_ARGS+=("-j$(nproc)")
  if [ "X${Z3_VERBOSE_BUILD_OUTPUT}" = "X1" ]; then
    GENERATOR_ARGS+=("VERBOSE=1")
  fi
elif [ "${Z3_CMAKE_GENERATOR}" = "Ninja" ]; then
  if [ "X${Z3_VERBOSE_BUILD_OUTPUT}" = "X1" ]; then
    GENERATOR_ARGS+=("-v")
  fi
else
  echo "Unknown CMake generator \"${Z3_CMAKE_GENERATOR}\""
  exit 1
fi
