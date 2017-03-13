################################################################################
# TPTP example
################################################################################
project(Z3_TPTP5 CXX)
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

add_executable(z3_tptp5 tptp5.cpp tptp5.lex.cpp)
target_include_directories(z3_tptp5 PRIVATE ${Z3_CXX_INCLUDE_DIRS})
target_link_libraries(z3_tptp5 PRIVATE ${Z3_LIBRARIES})

if ("${CMAKE_SYSTEM_NAME}" MATCHES "[Ww]indows")
  # On Windows we need to copy the Z3 libraries
  # into the same directory as the executable
  # so that they can be found.
  foreach (z3_lib ${Z3_LIBRARIES})
    message(STATUS "Adding copy rule for ${z3_lib}")
    add_custom_command(TARGET z3_tptp5
      POST_BUILD
      COMMAND
        ${CMAKE_COMMAND} -E copy_if_different
        $<TARGET_FILE:${z3_lib}>
        $<TARGET_FILE_DIR:z3_tptp5>
    )
  endforeach()
endif()

