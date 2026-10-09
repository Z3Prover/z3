cmake_minimum_required(VERSION 3.26)
project(Z3ClangTidy LANGUAGES C CXX)

# Plugins must use the same LLVM installation as the clang-tidy loading them.
find_package(LLVM 21.1.8 EXACT REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG HINTS "${LLVM_DIR}/../clang")
find_program(CLANG_TIDY NAMES clang-tidy-21 clang-tidy HINTS "${LLVM_TOOLS_BINARY_DIR}" REQUIRED)
execute_process(COMMAND "${CLANG_TIDY}" --version
  OUTPUT_VARIABLE tidy_version_output RESULT_VARIABLE tidy_version_status)
string(REGEX MATCH "[0-9]+\\.[0-9]+\\.[0-9]+" tidy_version "${tidy_version_output}")
if(NOT tidy_version_status EQUAL 0 OR NOT tidy_version STREQUAL LLVM_PACKAGE_VERSION)
  message(FATAL_ERROR "clang-tidy must match LLVM ${LLVM_PACKAGE_VERSION}; got '${tidy_version_output}'")
endif()

add_library(Z3TidyModule MODULE Z3Module.cpp AstArgumentOrderCheck.cpp)
target_compile_features(Z3TidyModule PRIVATE cxx_std_17)
target_include_directories(Z3TidyModule SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS} ${CLANG_INCLUDE_DIRS})
target_compile_options(Z3TidyModule PRIVATE -Wall -Wextra)
if(NOT LLVM_ENABLE_RTTI)
  target_compile_options(Z3TidyModule PRIVATE -fno-rtti)
endif()
# clang-tidy supplies the ClangTidy symbols. Do not link a second copy of its
# static registry into the plugin.
target_link_libraries(Z3TidyModule PRIVATE clang-cpp LLVM)
set_target_properties(Z3TidyModule PROPERTIES PREFIX "")
if(APPLE)
  target_link_options(Z3TidyModule PRIVATE "LINKER:-undefined,dynamic_lookup")
endif()
