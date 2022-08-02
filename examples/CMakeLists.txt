include(ExternalProject)

option(Z3_C_EXAMPLES_FORCE_CXX_LINKER
  "Force C++ linker when building C example projects" OFF)

if (Z3_C_EXAMPLES_FORCE_CXX_LINKER)
  # HACK: This is a workaround for UBSan.
  message(STATUS "Forcing C++ linker to be used when building example C projects")
  set(EXTERNAL_C_PROJ_USE_CXX_LINKER_ARG
    "-DFORCE_CXX_LINKER=ON"
  )
else()
  set(EXTERNAL_C_PROJ_USE_CXX_LINKER_ARG "")
endif()

if (DEFINED CMAKE_CONFIGURATION_TYPES)
  message(WARNING
    "Cannot set built type of external project when building with a "
    "multi-configuration generator")
  set(EXTERNAL_PROJECT_CMAKE_BUILD_TYPE_ARG "")
else()
  set(EXTERNAL_PROJECT_CMAKE_BUILD_TYPE_ARG
    "-DCMAKE_BUILD_TYPE:STRING=${CMAKE_BUILD_TYPE}"
  )
endif()

################################################################################
# Build example project using libz3's C API as an external project
################################################################################
ExternalProject_Add(c_example
  DEPENDS libz3
  # Configure step
  SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/c"
  CMAKE_ARGS
    "-DZ3_DIR=${PROJECT_BINARY_DIR}"
    "${EXTERNAL_C_PROJ_USE_CXX_LINKER_ARG}"
    "${EXTERNAL_PROJECT_CMAKE_BUILD_TYPE_ARG}"
  # Build step
  BUILD_ALWAYS ON
  BINARY_DIR "${CMAKE_CURRENT_BINARY_DIR}/c_example_build_dir"
  # Install Step
  INSTALL_COMMAND "${CMAKE_COMMAND}" -E echo "" # Dummy command
)
set_target_properties(c_example PROPERTIES EXCLUDE_FROM_ALL TRUE)

################################################################################
# Build maxsat example project using libz3's C API as an external project
################################################################################
ExternalProject_Add(c_maxsat_example
  DEPENDS libz3
  # Configure step
  SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/maxsat"
  CMAKE_ARGS
    "-DZ3_DIR=${PROJECT_BINARY_DIR}"
    "${EXTERNAL_C_PROJ_USE_CXX_LINKER_ARG}"
    "${EXTERNAL_PROJECT_CMAKE_BUILD_TYPE_ARG}"
  # Build step
  BUILD_ALWAYS ON
  BINARY_DIR "${CMAKE_CURRENT_BINARY_DIR}/c_maxsat_example_build_dir"
  # Install Step
  INSTALL_COMMAND "${CMAKE_COMMAND}" -E echo "" # Dummy command
)
set_target_properties(c_maxsat_example PROPERTIES EXCLUDE_FROM_ALL TRUE)


################################################################################
# Build example project using libz3's C++ API as an external project
################################################################################
ExternalProject_Add(cpp_example
  DEPENDS libz3
  # Configure step
  SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/c++"
  CMAKE_ARGS
    "-DZ3_DIR=${PROJECT_BINARY_DIR}"
    "${EXTERNAL_PROJECT_CMAKE_BUILD_TYPE_ARG}"
  # Build step
  BUILD_ALWAYS ON
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
  CMAKE_ARGS
    "-DZ3_DIR=${PROJECT_BINARY_DIR}"
    "${EXTERNAL_PROJECT_CMAKE_BUILD_TYPE_ARG}"
  # Build step
  BUILD_ALWAYS ON
  BINARY_DIR "${CMAKE_CURRENT_BINARY_DIR}/tptp_build_dir"
  # Install Step
  INSTALL_COMMAND "${CMAKE_COMMAND}" -E echo "" # Dummy command
)
set_target_properties(z3_tptp5 PROPERTIES EXCLUDE_FROM_ALL TRUE)

################################################################################
# Build example user-propagator project using libz3's C++ API as an external project
################################################################################
ExternalProject_Add(userPropagator
        DEPENDS libz3
        # Configure step
        SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/userPropagator"
        CMAKE_ARGS
        "-DZ3_DIR=${PROJECT_BINARY_DIR}"
        "${EXTERNAL_PROJECT_CMAKE_BUILD_TYPE_ARG}"
        # Build step
        BUILD_ALWAYS ON
        BINARY_DIR "${CMAKE_CURRENT_BINARY_DIR}/userPropagator_build_dir"
        # Install Step
        INSTALL_COMMAND "${CMAKE_COMMAND}" -E echo "" # Dummy command
        )
set_target_properties(userPropagator PROPERTIES EXCLUDE_FROM_ALL TRUE)

################################################################################
# Build Python examples
################################################################################
if (Z3_BUILD_PYTHON_BINDINGS)
  add_subdirectory(python)
endif()

################################################################################
# Build dotnet examples
################################################################################
if (Z3_BUILD_DOTNET_BINDINGS)
    add_subdirectory(dotnet)
endif()
