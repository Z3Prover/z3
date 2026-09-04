cmake_minimum_required(VERSION 3.5)

project(Z3_PACKAGE_TEST LANGUAGES CXX)

set(Z3_TEST_COMPONENT "" CACHE STRING
  "Z3 package component to request (static or shared)")
set(Z3_TEST_EXPECTED_TYPE "" CACHE STRING
  "Expected type of the imported z3::libz3 target")
set(Z3_TEST_CONFLICTING_COMPONENT "" CACHE STRING
  "Opposite Z3 package component that should be rejected")

if (Z3_TEST_COMPONENT)
  find_package(Z3 REQUIRED CONFIG COMPONENTS "${Z3_TEST_COMPONENT}")
else()
  find_package(Z3 REQUIRED CONFIG)
endif()

if (NOT TARGET z3::libz3)
  message(FATAL_ERROR "The Z3 package did not define z3::libz3")
endif()

if (Z3_TEST_CONFLICTING_COMPONENT)
  get_target_property(_z3_initial_type z3::libz3 TYPE)
  find_package(Z3 QUIET CONFIG COMPONENTS
    "${Z3_TEST_CONFLICTING_COMPONENT}")
  if (Z3_FOUND)
    message(FATAL_ERROR
      "Z3 accepted conflicting package component "
      "`${Z3_TEST_CONFLICTING_COMPONENT}`")
  endif()
  get_target_property(_z3_type_after_conflict z3::libz3 TYPE)
  if (NOT _z3_type_after_conflict STREQUAL _z3_initial_type)
    message(FATAL_ERROR "A conflicting package request replaced z3::libz3")
  endif()
endif()
if (Z3_TEST_EXPECTED_TYPE)
  get_target_property(_z3_actual_type z3::libz3 TYPE)
  if (NOT _z3_actual_type STREQUAL Z3_TEST_EXPECTED_TYPE)
    message(FATAL_ERROR
      "Expected z3::libz3 to be ${Z3_TEST_EXPECTED_TYPE}, "
      "but it is ${_z3_actual_type}")
  endif()
  if (_z3_actual_type STREQUAL "SHARED_LIBRARY" AND NOT Z3_SHARED_LIBS)
    message(FATAL_ERROR "The shared package did not set Z3_SHARED_LIBS")
  elseif (_z3_actual_type STREQUAL "STATIC_LIBRARY" AND Z3_SHARED_LIBS)
    message(FATAL_ERROR "The static package set Z3_SHARED_LIBS")
  endif()
endif()

add_executable(z3_package_test package_test.cpp)
target_link_libraries(z3_package_test PRIVATE z3::libz3)

enable_testing()
add_test(NAME z3_package_test COMMAND z3_package_test)
