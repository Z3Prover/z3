add_executable(cpp_example EXCLUDE_FROM_ALL example.cpp)
target_link_libraries(cpp_example PRIVATE libz3)
target_include_directories(cpp_example PRIVATE "${CMAKE_SOURCE_DIR}/src/api")
target_include_directories(cpp_example PRIVATE "${CMAKE_SOURCE_DIR}/src/api/c++")
