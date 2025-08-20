# Distributed under the OSI-approved BSD 3-Clause License.  See accompanying
# file Copyright.txt or https://cmake.org/licensing for details.

cmake_minimum_required(VERSION ${CMAKE_VERSION}) # this file comes with cmake

# If CMAKE_DISABLE_SOURCE_CHANGES is set to true and the source directory is an
# existing directory in our source tree, calling file(MAKE_DIRECTORY) on it
# would cause a fatal error, even though it would be a no-op.
if(NOT EXISTS "/home/runner/work/z3/z3/examples/c++")
  file(MAKE_DIRECTORY "/home/runner/work/z3/z3/examples/c++")
endif()
file(MAKE_DIRECTORY
  "/home/runner/work/z3/z3/test-cmake/examples/cpp_example_build_dir"
  "/home/runner/work/z3/z3/test-cmake/examples/cpp_example-prefix"
  "/home/runner/work/z3/z3/test-cmake/examples/cpp_example-prefix/tmp"
  "/home/runner/work/z3/z3/test-cmake/examples/cpp_example-prefix/src/cpp_example-stamp"
  "/home/runner/work/z3/z3/test-cmake/examples/cpp_example-prefix/src"
  "/home/runner/work/z3/z3/test-cmake/examples/cpp_example-prefix/src/cpp_example-stamp"
)

set(configSubDirs )
foreach(subDir IN LISTS configSubDirs)
    file(MAKE_DIRECTORY "/home/runner/work/z3/z3/test-cmake/examples/cpp_example-prefix/src/cpp_example-stamp/${subDir}")
endforeach()
if(cfgdir)
  file(MAKE_DIRECTORY "/home/runner/work/z3/z3/test-cmake/examples/cpp_example-prefix/src/cpp_example-stamp${cfgdir}") # cfgdir has leading slash
endif()
