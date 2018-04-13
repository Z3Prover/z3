
find_package(MlToolchain REQUIRED)

# Configure AssemblyInfo.cs
set(VER_MAJOR "${Z3_VERSION_MAJOR}")
set(VER_MINOR "${Z3_VERSION_MINOR}")
set(VER_BUILD "${Z3_VERSION_PATCH}")
set(VER_REVISION "${Z3_VERSION_TWEAK}")
set(Z3_ML_META_FILE "${CMAKE_CURRENT_BINARY_DIR}/META")
configure_file("META.in" "${Z3_ML_META_FILE}" @ONLY)

# Generate z3enum.ml
set(Z3_ML_NATIVE_FILE "${CMAKE_CURRENT_BINARY_DIR}/z3enums.ml")
add_custom_command(OUTPUT "${Z3_ML_NATIVE_FILE}"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${CMAKE_SOURCE_DIR}/scripts/update_api.py"
    "--ml-src-dir"
    "${CMAKE_CURRENT_BINARY_DIR}/"
    "--ml-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${CMAKE_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
    # FIXME: When update_api.py no longer uses ``mk_util`` drop this dependency
    "${CMAKE_SOURCE_DIR}/scripts/mk_util.py"
  COMMENT "Generating ${Z3_ML_NATIVE_FILE}"
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)

set(Z3_ML_ASSEMBLY_SOURCES_IN_SRC_TREE
  z3native.ml.pre
  z3.ml
  z3.mli
)

set(Z3_ML_ASSEMBLY_SOURCES "")
# Make paths to source files absolute
foreach (file ${Z3_ML_ASSEMBLY_SOURCES_IN_SRC_TREE})
  list(APPEND Z3_ML_ASSEMBLY_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/${file}")
endforeach()

# Add generated files
list(APPEND Z3_ML_ASSEMBLY_SOURCES
  "${Z3_ML_CONST_FILE}"
  "${Z3_ML_NATIVE_FILE}"
)

set(OCAMLC_FLAGS "")

# Common flags
list(APPEND OCAMLC_FLAGS
  "-I"
  "${CMAKE_CURRENT_BINARY_DIR}"
)

# Set the build type flags. The build type for the assembly roughly corresponds
# with the native code build type.
list(APPEND OCAMLC_FLAGS
  # Debug flags, expands to nothing if we aren't doing a debug build
  "$<$<CONFIG:Debug>:-g>"
)

set(Z3_ML_ASSEMBLY_OUTPUT_DIR "${CMAKE_BINARY_DIR}")
set(Z3_ML_BYTECODE_LIB "${Z3_ML_ASSEMBLY_OUTPUT_DIR}/z3.cma")
set(Z3_ML_NATIVE_LIB "${Z3_ML_ASSEMBLY_OUTPUT_DIR}/z3.cmxa")
set(Z3_ML_DYN_NATIVE_LIB "${Z3_ML_ASSEMBLY_OUTPUT_DIR}/z3.cmxs")
add_custom_command(OUTPUT "${Z3_ML_BYTECODE_LIB}"
  COMMAND
    "${OCAMLC_EXECUTABLE}"
    ${OCAMLC_FLAGS}
    "-o ${Z3_ML_BYTECODE_LIB}"
    ${Z3_ML_ASSEMBLY_SOURCES}
  DEPENDS
    ${Z3_ML_ASSEMBLY_SOURCES}
    libz3
  WORKING_DIRECTORY "${Z3_ML_ASSEMBLY_OUTPUT_DIR}"
  COMMENT "Building \"${Z3_ML_BYTECODE_LIB}\""
)
add_custom_command(OUTPUT "${Z3_ML_NATIVE_LIB}"
  COMMAND
    "${OCAMLOPT_EXECUTABLE}"
    ${OCAMLC_FLAGS}
    "-o ${Z3_ML_NATIVE_LIB}"
    ${Z3_ML_ASSEMBLY_SOURCES}
  DEPENDS
    ${Z3_ML_ASSEMBLY_SOURCES}
    libz3
  WORKING_DIRECTORY "${Z3_ML_ASSEMBLY_OUTPUT_DIR}"
  COMMENT "Building \"${Z3_ML_NATIVE_LIB}\""
)
add_custom_command(OUTPUT "${Z3_ML_DYN_NATIVE_LIB}"
  COMMAND
    "${OCAMLOPT_EXECUTABLE}"
    ${OCAMLC_FLAGS}
    "-linkall -shared"
    "-o ${Z3_ML_DYN_NATIVE_LIB}"
    ${Z3_ML_NATIVE_LIB}
  DEPENDS
    ${Z3_ML_NATIVE_LIB}
    libz3
  WORKING_DIRECTORY "${Z3_ML_ASSEMBLY_OUTPUT_DIR}"
  COMMENT "Building \"${Z3_ML_NATIVE_LIB}\""
)

# Convenient top-level target
add_custom_target(build_z3_ml_bindings
  ALL
  DEPENDS
    "${Z3_ML_BYTECODE_LIB}"
    "${Z3_ML_NATIVE_LIB}"
)

###############################################################################
# Install
###############################################################################
#option(INSTALL_ML_BINDINGS "Install .NET bindings when invoking install target" ON)
#set(GAC_PKG_NAME "Microsoft.Z3.Sharp")
#set(PREFIX "${CMAKE_INSTALL_PREFIX}")
#set(VERSION "${Z3_VERSION}")
#set(Z3_ML_PKGCONFIG_FILE "${CMAKE_CURRENT_BINARY_DIR}/Microsoft.Z3.Sharp.pc")
#configure_file("Microsoft.Z3.Sharp.pc.in" "${Z3_ML_PKGCONFIG_FILE}" @ONLY)
#
#if (ML_TOOLCHAIN_IS_MONO)
#  message(STATUS "Emitting install rules for .NET bindings")
#  # Install pkgconfig file for the assembly. This is needed by Monodevelop
#  # to find the assembly
#  install(FILES "${Z3_ML_PKGCONFIG_FILE}" DESTINATION "${CMAKE_INSTALL_PKGCONFIGDIR}")
#
#  # Configure the install and uninstall scripts.
#  # Note: If multi-configuration generator support is ever fixed then these
#  # scripts will be broken.
#  configure_file(cmake_install_gac.cmake.in cmake_install_gac.cmake @ONLY)
#  configure_file(cmake_uninstall_gac.cmake.in cmake_uninstall_gac.cmake @ONLY)
#
#  # Tell CMake to Invoke a script to install assembly to the GAC during install
#  install(SCRIPT "${CMAKE_CURRENT_BINARY_DIR}/cmake_install_gac.cmake")
#
#  # Add custom target to uninstall the assembly from the GAC
#  add_custom_target(remove_dotnet_dll_from_gac
#    COMMAND "${CMAKE_COMMAND}" "-P" "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall_gac.cmake"
#    COMMENT "Uninstalling ${Z3_ML_ASSEMBLY_NAME} from the GAC"
#    ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
#  )
#  add_dependencies(uninstall remove_dotnet_dll_from_gac)
#
#elseif(ML_TOOLCHAIN_IS_WINDOWS)
#  # Don't install Z3_ML_ASSEMBLY_DLL into the gac. Instead just copy into
#  # installation directory.
#  install(FILES "${Z3_ML_ASSEMBLY_DLL}" DESTINATION "${CMAKE_INSTALL_LIBDIR}")
#  install(FILES "${Z3_ML_ASSEMBLY_DLL_DOC}" DESTINATION "${CMAKE_INSTALL_LIBDIR}")
#else()
#  message(FATAL_ERROR "Unknown .NET toolchain")
#endif()
