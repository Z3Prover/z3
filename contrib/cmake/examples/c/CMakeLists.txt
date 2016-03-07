add_executable(c_example EXCLUDE_FROM_ALL test_capi.c)
target_link_libraries(c_example PRIVATE libz3)
target_include_directories(c_example PRIVATE "${CMAKE_SOURCE_DIR}/src/api")
