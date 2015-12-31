cmake_minimum_required(VERSION 3.3)

project(z3)

set(CMAKE_BUILD_TYPE Debug)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/cmake/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/cmake/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/cmake/bin)
set(CMAKE_CXX_FLAGS "-O0 -std=c++11 -D_NO_OMP_ -D_MP_GMP -Wno-deprecated-register -Wno-implicit-function-declaration")

find_package(JNI)

add_definitions(-D_AMD64_ -D_TRACE)

link_libraries(gmp)

file(STRINGS cmake/include-dirs.txt INCLUDE_DIRS)
file(STRINGS cmake/sources-z3.txt EXE_SOURCE_FILES)
file(STRINGS cmake/sources-libz3.txt LIB_SOURCE_FILES)

include_directories(${JNI_INCLUDE_DIRS} ${INCLUDE_DIRS})

add_library(z3 SHARED ${LIB_SOURCE_FILES})

add_executable(z3-command ${EXE_SOURCE_FILES})
set_target_properties(z3-command PROPERTIES OUTPUT_NAME z3)
target_link_libraries(z3-command z3)

add_executable(example examples/c++/example.cpp)
target_link_libraries(example z3)

add_library(z3java SHARED src/api/java/Native.cpp)
target_link_libraries(z3java z3)
