# This file overrides the default compiler flags for CMake's built-in
# configurations (CMAKE_BUILD_TYPE). Most compiler flags should not be set here.
# The main purpose is to have very fine grained control of the compiler flags.

# We only override the defaults for Clang and GCC right now.
# CMake's MSVC logic is complicated so for now it's better to just inherit CMake's defaults.
if (("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang") OR ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU"))
  # Taken from Modules/Compiler/GNU.cmake
  set(CMAKE_CXX_FLAGS_INIT "")
  set(CMAKE_CXX_FLAGS_DEBUG_INIT "-g -O0")
  set(CMAKE_CXX_FLAGS_MINSIZEREL_INIT "-Os -DNDEBUG")
  set(CMAKE_CXX_FLAGS_RELEASE_INIT "-O3 -DNDEBUG")
  set(CMAKE_CXX_FLAGS_RELWITHDEBINFO_INIT "-O2 -g -DNDEBUG")
endif()
