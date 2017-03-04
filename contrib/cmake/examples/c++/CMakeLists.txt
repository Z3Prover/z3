################################################################################
# Example C++ project
################################################################################
project(Z3_C_EXAMPLE CXX)
cmake_minimum_required(VERSION 2.8.12)
find_package(Z3
  REQUIRED
  CONFIG
  # `NO_DEFAULT_PATH` is set so that -DZ3_DIR has to be passed to find Z3.
  # This should prevent us from accidently picking up an installed
  # copy of Z3. This is here to benefit Z3's build sytem when building
  # this project. When making your own project you probably shouldn't
  # use this option.
  NO_DEFAULT_PATH
)
message(STATUS "Z3_FOUND: ${Z3_FOUND}")
message(STATUS "Found Z3 ${Z3_VERSION_STRING}")
message(STATUS "Z3_DIR: ${Z3_DIR}")

add_executable(cpp_example example.cpp)
target_include_directories(cpp_example PRIVATE ${Z3_CXX_INCLUDE_DIRS})
target_link_libraries(cpp_example PRIVATE ${Z3_LIBRARIES})
