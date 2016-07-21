add_executable(tptp5 EXCLUDE_FROM_ALL tptp5.cpp)
target_link_libraries(tptp5 PRIVATE libz3)
target_include_directories(tptp5 PRIVATE "${CMAKE_SOURCE_DIR}/src/api")
target_include_directories(tptp5 PRIVATE "${CMAKE_SOURCE_DIR}/src/api/c++")
