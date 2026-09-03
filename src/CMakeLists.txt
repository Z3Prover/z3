cmake_dependent_option(Z3_BUILD_EXECUTABLE
    "Build the z3 executable" ON
    "PROJECT_IS_TOP_LEVEL;Z3_BUILD_LIBZ3_CORE" OFF)
cmake_dependent_option(Z3_BUILD_TEST_EXECUTABLES
    "Build test executables" ON
    "PROJECT_IS_TOP_LEVEL;Z3_BUILD_LIBZ3_CORE" OFF)

################################################################################
# Traverse direct children. Each directory adds its own direct children.
################################################################################
add_subdirectory(ackermannization)
add_subdirectory(api)
add_subdirectory(ast)
add_subdirectory(cmd_context)
add_subdirectory(math)
add_subdirectory(model)
add_subdirectory(muz)
add_subdirectory(nlsat)
add_subdirectory(opt)
add_subdirectory(params)
add_subdirectory(parsers)
add_subdirectory(qe)
add_subdirectory(sat)
if (Z3_BUILD_EXECUTABLE)
  add_subdirectory(shell)
endif()
add_subdirectory(smt)
add_subdirectory(solver)
add_subdirectory(tactic)
if (Z3_BUILD_TEST_EXECUTABLES)
  add_subdirectory(test)
endif()
add_subdirectory(util)
################################################################################
# libz3
################################################################################
target_sources(libz3 PUBLIC
  FILE_SET c_headers
  TYPE HEADERS
  BASE_DIRS "${CMAKE_CURRENT_SOURCE_DIR}/api"
  FILES
    api/z3_algebraic.h
    api/z3_api.h
    api/z3_ast_containers.h
    api/z3_fixedpoint.h
    api/z3_fpa.h
    api/z3.h
    api/z3_macros.h
    api/z3_optimization.h
    api/z3_polynomial.h
    api/z3_rcf.h
    api/z3_spacer.h
    api/z3_v1.h
  FILE_SET cxx_headers
  TYPE HEADERS
  BASE_DIRS "${CMAKE_CURRENT_SOURCE_DIR}/api/c++"
  FILES api/c++/z3++.h
  FILE_SET generated_headers
  TYPE HEADERS
  BASE_DIRS "${CMAKE_CURRENT_BINARY_DIR}/util"
  FILES "${CMAKE_CURRENT_BINARY_DIR}/util/z3_version.h")
set_target_properties(libz3 PROPERTIES
  # VERSION determines the version in the filename of the shared library.
  # SOVERSION determines the value of the DT_SONAME field on ELF platforms.
  # On ELF platforms the final compiled filename will be libz3.so.W.X.Y.Z
  # but symlinks will be made to this file from libz3.so and also from
  # libz3.so.W.X.
  # This indicates that no breaking API changes will be made within a single
  # minor version.
  VERSION ${Z3_VERSION}
  SOVERSION ${Z3_VERSION_MAJOR}.${Z3_VERSION_MINOR})

# Set macOS-specific properties for proper .dylib versioning (fixes issue #6651)
if (CMAKE_SYSTEM_NAME STREQUAL "Darwin")
  set_target_properties(libz3 PROPERTIES
    # Use @rpath for install name to make library relocatable
    INSTALL_NAME_DIR "@rpath"
    # Enable RPATH support
    MACOSX_RPATH TRUE
  )
  # Add header padding to allow install_name_tool to modify the dylib
  # This fixes issues where install_name_tool fails with "larger updated load commands do not fit"
  # See: https://github.com/Z3Prover/z3/issues/7623
  target_link_options(libz3 PRIVATE "-Wl,-headerpad_max_install_names")
endif()

if (NOT MSVC)
  # On UNIX like platforms if we don't change the OUTPUT_NAME
  # the library gets a name like ``liblibz3.so`` so we change it
  # here. We don't do a rename with MSVC because we get file naming
  # conflicts (the z3 executable also has this OUTPUT_NAME) with
  # ``.ilk``, ``.pdb``, ``.lib`` and ``.exp`` files sharing the same
  # prefix.
  set_target_properties(libz3 PROPERTIES OUTPUT_NAME z3)
elseif (WIN32 AND NOT BUILD_SHARED_LIBS)
  # A shared build installs libz3.lib as its import library. Give the static
  # archive a distinct name so both variants can share an install prefix.
  set_target_properties(libz3 PROPERTIES OUTPUT_NAME libz3-static)
endif()

# The `PRIVATE` usage requirement is specified so that when building Z3 as a
# shared library the dependent libraries are specified on the link command line
# so that if those are also shared libraries they are referenced by `libz3.so`.
target_link_libraries(libz3 PRIVATE z3_common)

install(TARGETS libz3 z3_common
  EXPORT Z3_EXPORTED_TARGETS
  LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}"
  ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}" # On Windows this installs ``libz3.lib`` which CMake calls the "corresponding import library". Do we want this installed?
  RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}" # For Windows. DLLs are runtime targets for CMake
  FILE_SET c_headers DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}"
  FILE_SET cxx_headers DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}"
  FILE_SET generated_headers DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}"
)

if (MSVC)
  # Generate the module-definition file used to export the C API. Listing the
  # generated file as a source gives CMake both the build dependency and the
  # linker input without a separate custom target.
  set(dll_module_exports_file "${CMAKE_CURRENT_BINARY_DIR}/api_dll.def")
  add_custom_command(OUTPUT "${dll_module_exports_file}"
    COMMAND
      "${Python3_EXECUTABLE}"
      "${PROJECT_SOURCE_DIR}/scripts/mk_def_file.py"
      "${dll_module_exports_file}"
      "libz3"
      ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    DEPENDS
      "${PROJECT_SOURCE_DIR}/scripts/mk_def_file.py"
      ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
      ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    COMMENT "Generating \"${dll_module_exports_file}\""
    USES_TERMINAL
    VERBATIM
  )
  target_sources(libz3 PRIVATE "${dll_module_exports_file}")
endif()
