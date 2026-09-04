################################################################################
# Example C++ project
################################################################################
cmake_minimum_required(VERSION 3.12)
project(Z3_USER_PROPAGATOR_EXAMPLE CXX)
find_package(Z3
  REQUIRED
  CONFIG
  # `NO_DEFAULT_PATH` is set so that -DZ3_DIR has to be passed to find Z3.
  # This should prevent us from accidentally picking up an installed
  # copy of Z3. This is here to benefit Z3's build system when building
  # this project. When making your own project you probably shouldn't
  # use this option.
  NO_DEFAULT_PATH
)

message(STATUS "Z3_FOUND: ${Z3_FOUND}")
message(STATUS "Found Z3 ${Z3_VERSION_STRING}")
message(STATUS "Z3_DIR: ${Z3_DIR}")

add_executable(user_propagator_example
        example.cpp
        common.h
        user_propagator.h
        user_propagator_with_theory.h
        user_propagator_subquery_maximisation.h
        user_propagator_internal_maximisation.h
        user_propagator_created_maximisation.h)

target_compile_features(user_propagator_example PRIVATE cxx_std_20)
target_link_libraries(user_propagator_example PRIVATE z3::libz3)

if (CMAKE_SYSTEM_NAME MATCHES "[Ww]indows")
  # On Windows we need to copy the Z3 libraries
  # into the same directory as the executable
  # so that they can be found.
  add_custom_command(TARGET user_propagator_example POST_BUILD
    COMMAND ${CMAKE_COMMAND} -E copy_if_different
      $<TARGET_FILE:z3::libz3> $<TARGET_FILE_DIR:user_propagator_example>)
endif()
