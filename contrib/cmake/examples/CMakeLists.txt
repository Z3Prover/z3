include(ExternalProject)
# Unfortunately `BUILD_ALWAYS` only seems to be supported with the version of ExternalProject
# that shipped with CMake >= 3.1.
if (("${CMAKE_VERSION}" VERSION_EQUAL "3.1") OR ("${CMAKE_VERSION}" VERSION_GREATER "3.1"))
  set(EXTERNAL_PROJECT_BUILD_ALWAYS_ARG BUILD_ALWAYS 1)
else()
  set(EXTERNAL_PROJECT_BUILD_ALWAYS_ARG "")
endif()

################################################################################
# Build example project using libz3's C API as an external project
################################################################################
ExternalProject_Add(c_example
  DEPENDS libz3
  # Configure step
  SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/c"
  CMAKE_ARGS "-DZ3_DIR=${CMAKE_BINARY_DIR}"
  # Build step
  ${EXTERNAL_PROJECT_BUILD_ALWAYS_ARG}
  BINARY_DIR "${CMAKE_CURRENT_BINARY_DIR}/c_example_build_dir"
  # Install Step
  INSTALL_COMMAND "${CMAKE_COMMAND}" -E echo "" # Dummy command
)
set_target_properties(c_example PROPERTIES EXCLUDE_FROM_ALL TRUE)


################################################################################
# Build example project using libz3's C++ API as an external project
################################################################################
ExternalProject_Add(cpp_example
  DEPENDS libz3
  # Configure step
  SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/c++"
  CMAKE_ARGS "-DZ3_DIR=${CMAKE_BINARY_DIR}"
  # Build step
  ${EXTERNAL_PROJECT_BUILD_ALWAYS_ARG}
  BINARY_DIR "${CMAKE_CURRENT_BINARY_DIR}/cpp_example_build_dir"
  # Install Step
  INSTALL_COMMAND "${CMAKE_COMMAND}" -E echo "" # Dummy command
)
set_target_properties(cpp_example PROPERTIES EXCLUDE_FROM_ALL TRUE)

################################################################################
# Build example tptp5 project using libz3's C++ API as an external project
################################################################################
ExternalProject_Add(z3_tptp5
  DEPENDS libz3
  # Configure step
  SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/tptp"
  CMAKE_ARGS "-DZ3_DIR=${CMAKE_BINARY_DIR}"
  # Build step
  ${EXTERNAL_PROJECT_BUILD_ALWAYS_ARG}
  BINARY_DIR "${CMAKE_CURRENT_BINARY_DIR}/tptp_build_dir"
  # Install Step
  INSTALL_COMMAND "${CMAKE_COMMAND}" -E echo "" # Dummy command
)
set_target_properties(z3_tptp5 PROPERTIES EXCLUDE_FROM_ALL TRUE)

################################################################################
# Build Python examples
################################################################################
if (BUILD_PYTHON_BINDINGS)
  add_subdirectory(python)
endif()
