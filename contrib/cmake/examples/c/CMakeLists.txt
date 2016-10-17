# FIXME: We should build this as an external project and consume
# Z3 as `find_package(z3 CONFIG)`.
add_executable(c_example EXCLUDE_FROM_ALL test_capi.c)
target_link_libraries(c_example PRIVATE libz3)
target_include_directories(c_example PRIVATE "${CMAKE_SOURCE_DIR}/src/api")
# This is needed for when libz3 is built as a static library
if (NOT BUILD_LIBZ3_SHARED)
  z3_append_linker_flag_list_to_target(c_example ${Z3_DEPENDENT_EXTRA_C_LINK_FLAGS})
endif()
