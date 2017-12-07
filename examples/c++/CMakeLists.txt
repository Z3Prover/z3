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

################################################################################
# Z3 C++ API bindings require C++11
################################################################################
if ("${CMAKE_VERSION}" VERSION_LESS "3.1")
  # Legacy CMake support
  if (("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU") OR ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang"))
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
  else()
    message(FATAL_ERROR "Setting C++ version to C++11 not supported for \"${CMAKE_CXX_COMPILER_ID}\"")
  endif()
else ()
  set(CMAKE_CXX_STANDARD 11)
  set(CMAKE_CXX_STANDARD_REQUIRED ON)
endif ()

message(STATUS "Z3_FOUND: ${Z3_FOUND}")
message(STATUS "Found Z3 ${Z3_VERSION_STRING}")
message(STATUS "Z3_DIR: ${Z3_DIR}")

add_executable(cpp_example example.cpp)
target_include_directories(cpp_example PRIVATE ${Z3_CXX_INCLUDE_DIRS})
target_link_libraries(cpp_example PRIVATE ${Z3_LIBRARIES})

if ("${CMAKE_SYSTEM_NAME}" MATCHES "[Ww]indows")
  # On Windows we need to copy the Z3 libraries
  # into the same directory as the executable
  # so that they can be found.
  foreach (z3_lib ${Z3_LIBRARIES})
    message(STATUS "Adding copy rule for ${z3_lib}")
    add_custom_command(TARGET cpp_example
      POST_BUILD
      COMMAND
        ${CMAKE_COMMAND} -E copy_if_different
        $<TARGET_FILE:${z3_lib}>
        $<TARGET_FILE_DIR:cpp_example>
    )
  endforeach()
endif()
