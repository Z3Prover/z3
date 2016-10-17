# FIXME: We should build this as an external project and consume
# Z3 as `find_package(z3 CONFIG)`.
add_executable(cpp_example EXCLUDE_FROM_ALL example.cpp)
target_link_libraries(cpp_example PRIVATE libz3)
target_include_directories(cpp_example PRIVATE "${CMAKE_SOURCE_DIR}/src/api")
target_include_directories(cpp_example PRIVATE "${CMAKE_SOURCE_DIR}/src/api/c++")
if (NOT BUILD_LIBZ3_SHARED)
  z3_append_linker_flag_list_to_target(cpp_example ${Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS})
endif()
