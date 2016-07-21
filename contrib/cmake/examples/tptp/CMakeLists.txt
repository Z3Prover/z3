add_executable(z3_tptp5 EXCLUDE_FROM_ALL tptp5.cpp tptp5.lex.cpp)
target_link_libraries(z3_tptp5 PRIVATE libz3)
target_include_directories(z3_tptp5 PRIVATE "${CMAKE_SOURCE_DIR}/src/api")
target_include_directories(z3_tptp5 PRIVATE "${CMAKE_SOURCE_DIR}/src/api/c++")
