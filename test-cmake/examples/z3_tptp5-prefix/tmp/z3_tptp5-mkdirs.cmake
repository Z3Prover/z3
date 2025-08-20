# Distributed under the OSI-approved BSD 3-Clause License.  See accompanying
# file Copyright.txt or https://cmake.org/licensing for details.

cmake_minimum_required(VERSION ${CMAKE_VERSION}) # this file comes with cmake

# If CMAKE_DISABLE_SOURCE_CHANGES is set to true and the source directory is an
# existing directory in our source tree, calling file(MAKE_DIRECTORY) on it
# would cause a fatal error, even though it would be a no-op.
if(NOT EXISTS "/home/runner/work/z3/z3/examples/tptp")
  file(MAKE_DIRECTORY "/home/runner/work/z3/z3/examples/tptp")
endif()
file(MAKE_DIRECTORY
  "/home/runner/work/z3/z3/test-cmake/examples/tptp_build_dir"
  "/home/runner/work/z3/z3/test-cmake/examples/z3_tptp5-prefix"
  "/home/runner/work/z3/z3/test-cmake/examples/z3_tptp5-prefix/tmp"
  "/home/runner/work/z3/z3/test-cmake/examples/z3_tptp5-prefix/src/z3_tptp5-stamp"
  "/home/runner/work/z3/z3/test-cmake/examples/z3_tptp5-prefix/src"
  "/home/runner/work/z3/z3/test-cmake/examples/z3_tptp5-prefix/src/z3_tptp5-stamp"
)

set(configSubDirs )
foreach(subDir IN LISTS configSubDirs)
    file(MAKE_DIRECTORY "/home/runner/work/z3/z3/test-cmake/examples/z3_tptp5-prefix/src/z3_tptp5-stamp/${subDir}")
endforeach()
if(cfgdir)
  file(MAKE_DIRECTORY "/home/runner/work/z3/z3/test-cmake/examples/z3_tptp5-prefix/src/z3_tptp5-stamp${cfgdir}") # cfgdir has leading slash
endif()
