################################################################################
# Example maxsat project
################################################################################
# NOTE: Even though this is a C project, libz3 uses C++. When using libz3
# as a static library if we don't configure this project to also support
# C++ we will use the C linker rather than the C++ linker and will not link
# the C++ standard library in resulting in a link failure.
project(Z3_C_MAXSAT_EXAMPLE C CXX)
cmake_minimum_required(VERSION 3.4)
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

add_executable(c_maxsat_example maxsat.c)
target_include_directories(c_maxsat_example PRIVATE ${Z3_C_INCLUDE_DIRS})
target_link_libraries(c_maxsat_example PRIVATE ${Z3_LIBRARIES})

option(FORCE_CXX_LINKER "Force linker with C++ linker" OFF)
if (FORCE_CXX_LINKER)
  # This is a hack for avoiding UBSan linking errors
  message(STATUS "Forcing use of C++ linker")
  set_target_properties(c_maxsat_example
    PROPERTIES
    LINKER_LANGUAGE CXX
  )
endif()

if ("${CMAKE_SYSTEM_NAME}" MATCHES "[Ww]indows")
  # On Windows we need to copy the Z3 libraries
  # into the same directory as the executable
  # so that they can be found.
  foreach (z3_lib ${Z3_LIBRARIES})
    message(STATUS "Adding copy rule for ${z3_lib}")
    add_custom_command(TARGET c_maxsat_example
      POST_BUILD
      COMMAND
        ${CMAKE_COMMAND} -E copy_if_different
        $<TARGET_FILE:${z3_lib}>
        $<TARGET_FILE_DIR:c_maxsat_example>
    )
  endforeach()
endif()
