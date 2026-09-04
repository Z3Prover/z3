################################################################################
# Example C project
################################################################################
# NOTE: Even though this is a C project, libz3 uses C++. When using libz3
# as a static library if we don't configure this project to also support
# C++ we will use the C linker rather than the C++ linker and will not link
# the C++ standard library in resulting in a link failure.
cmake_minimum_required(VERSION 3.5)
project(Z3_C_EXAMPLE C CXX)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_STANDARD 99)
set(CMAKE_C_EXTENSIONS OFF)

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

add_executable(c_example test_capi.c)

option(FORCE_CXX_LINKER "Force linker with C++ linker" OFF)
if (FORCE_CXX_LINKER)
  # This is a hack for avoiding UBSan linking errors
  message(STATUS "Forcing use of C++ linker")
  set_target_properties(c_example
    PROPERTIES
    LINKER_LANGUAGE CXX
  )
endif()

target_link_libraries(c_example PRIVATE z3::libz3)

if (CMAKE_SYSTEM_NAME MATCHES "[Ww]indows")
  # On Windows we need to copy the Z3 libraries
  # into the same directory as the executable
  # so that they can be found.
  add_custom_command(TARGET c_example POST_BUILD
    COMMAND ${CMAKE_COMMAND} -E copy_if_different
      $<TARGET_FILE:z3::libz3> $<TARGET_FILE_DIR:c_example>)
endif()
