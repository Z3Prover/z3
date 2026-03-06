################################################################################
# Traverse directories each adding a Z3 component
################################################################################
# I'm duplicating the order in ``mk_project.py`` for now to help us keep
# the build systems in sync.
#
# The components in these directory explicitly declare their dependencies so
# you may be able to re-order some of these directories but an error will be
# raised if you try to declare a component is dependent on another component
# that has not yet been declared.
add_subdirectory(util)
add_subdirectory(math/polynomial)
add_subdirectory(math/dd)
add_subdirectory(math/hilbert)
add_subdirectory(math/simplex)
add_subdirectory(math/interval)
add_subdirectory(math/realclosure)
add_subdirectory(math/subpaving)
add_subdirectory(ast)
add_subdirectory(params)
add_subdirectory(ast/rewriter)
add_subdirectory(ast/rewriter/bit_blaster)
add_subdirectory(ast/normal_forms)
add_subdirectory(ast/macros)
add_subdirectory(model)
add_subdirectory(ast/euf)
add_subdirectory(ast/converters)
add_subdirectory(ast/substitution)
add_subdirectory(ast/simplifiers)
add_subdirectory(tactic)
add_subdirectory(qe/mbp)
add_subdirectory(qe/lite)
add_subdirectory(parsers/util)
add_subdirectory(math/grobner)
add_subdirectory(sat)
add_subdirectory(nlsat)
add_subdirectory(tactic/core)
add_subdirectory(math/subpaving/tactic)
add_subdirectory(tactic/aig)
add_subdirectory(tactic/arith)
add_subdirectory(solver)
add_subdirectory(cmd_context)
add_subdirectory(cmd_context/extra_cmds)
add_subdirectory(parsers/smt2)
add_subdirectory(solver/assertions)
add_subdirectory(ast/pattern)
add_subdirectory(math/lp)
add_subdirectory(ast/sls)
add_subdirectory(sat/smt)
add_subdirectory(sat/tactic)
add_subdirectory(nlsat/tactic)
add_subdirectory(ackermannization)
add_subdirectory(ast/proofs)
add_subdirectory(ast/fpa)
add_subdirectory(smt/proto_model)
add_subdirectory(smt)
add_subdirectory(tactic/bv)
add_subdirectory(smt/tactic)
add_subdirectory(tactic/sls)
add_subdirectory(qe)
add_subdirectory(muz/base)
add_subdirectory(muz/dataflow)
add_subdirectory(muz/transforms)
add_subdirectory(muz/rel)
add_subdirectory(muz/clp)
add_subdirectory(muz/tab)
add_subdirectory(muz/bmc)
add_subdirectory(muz/ddnf)
add_subdirectory(muz/spacer)
add_subdirectory(muz/fp)
add_subdirectory(tactic/ufbv)
add_subdirectory(sat/sat_solver)
add_subdirectory(tactic/smtlogics)
add_subdirectory(tactic/fpa)
add_subdirectory(tactic/fd_solver)
add_subdirectory(tactic/portfolio)
add_subdirectory(opt)
add_subdirectory(api)
add_subdirectory(api/dll)
################################################################################
# libz3
################################################################################
get_property(Z3_LIBZ3_COMPONENTS_LIST GLOBAL PROPERTY Z3_LIBZ3_COMPONENTS)
set (object_files "")
foreach (component ${Z3_LIBZ3_COMPONENTS_LIST})
  list(APPEND object_files $<TARGET_OBJECTS:${component}>)
endforeach()
if (Z3_BUILD_LIBZ3_SHARED)
  set(lib_type "SHARED")
else()
  set(lib_type "STATIC")
endif()
# Enable static msvc runtime.
if (MSVC AND Z3_BUILD_LIBZ3_MSVC_STATIC)
    set(CompilerFlags
        CMAKE_CXX_FLAGS
        CMAKE_CXX_FLAGS_DEBUG
        CMAKE_CXX_FLAGS_RELEASE
        CMAKE_CXX_FLAGS_MINSIZEREL
        CMAKE_CXX_FLAGS_RELWITHDEBINFO
        CMAKE_C_FLAGS
        CMAKE_C_FLAGS_DEBUG
        CMAKE_C_FLAGS_RELEASE
        CMAKE_C_FLAGS_MINSIZEREL
        CMAKE_C_FLAGS_RELWITHDEBINFO
        )
    foreach(CompilerFlag ${CompilerFlags})
        string(REPLACE "/MD" "/MT" ${CompilerFlag} "${${CompilerFlag}}")
        string(REPLACE "/MDd" "/MTd" ${CompilerFlag} "${${CompilerFlag}}")
        set(${CompilerFlag} "${${CompilerFlag}}" CACHE STRING "msvc compiler flags" FORCE)
        message("MSVC flags: ${CompilerFlag}:${${CompilerFlag}}")
    endforeach()
endif()
add_library(libz3 ${lib_type} ${object_files})
target_include_directories(libz3 INTERFACE
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/api>
  $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>)
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
endif()

# The `PRIVATE` usage requirement is specified so that when building Z3 as a
# shared library the dependent libraries are specified on the link command line
# so that if those are also shared libraries they are referenced by `libz3.so`.
target_link_libraries(libz3 PRIVATE ${Z3_DEPENDENT_LIBS})

# On macOS, add headerpad for install_name_tool compatibility
if(CMAKE_SYSTEM_NAME STREQUAL "Darwin" AND Z3_BUILD_LIBZ3_SHARED)
  target_link_options(libz3 PRIVATE "-Wl,-headerpad_max_install_names")
endif()

################################################################################
# Create include directory with headers for easier developer integration
################################################################################
set(Z3_BUILD_INCLUDE_DIR "${CMAKE_BINARY_DIR}/include")
file(MAKE_DIRECTORY "${Z3_BUILD_INCLUDE_DIR}")

# Copy Z3 API headers to build include directory
set(Z3_API_HEADERS
  api/z3.h
  api/z3_api.h
  api/z3_algebraic.h
  api/z3_ast_containers.h
  api/z3_fixedpoint.h
  api/z3_fpa.h
  api/z3_logger.h
  api/z3_macros.h
  api/z3_optimization.h
  api/z3_polynomial.h
  api/z3_private.h
  api/z3_rcf.h
  api/z3_replayer.h
  api/z3_spacer.h
  api/z3_v1.h
  api/c++/z3++.h
)

# Create custom target to copy headers
#add_custom_target(z3_headers_copy ALL
#  COMMENT "Copying Z3 API headers to build include directory"
#)
#
#foreach(header_file ${Z3_API_HEADERS})
#  get_filename_component(header_name "${header_file}" NAME)
#  set(src_file "${CMAKE_CURRENT_SOURCE_DIR}/${header_file}")
#  set(dst_file "${Z3_BUILD_INCLUDE_DIR}/${header_name}")
#
#  add_custom_command(
#    TARGET z3_headers_copy POST_BUILD
#    COMMAND ${CMAKE_COMMAND} -E copy_if_different
#            "${src_file}"
#            "${dst_file}"
#    COMMENT "Copying ${header_name} to include directory"
#    VERBATIM
#  )
#endforeach()

# Make libz3 depend on header copying
#add_dependencies(libz3 z3_headers_copy)

# Update libz3 to also expose the build include directory
target_include_directories(libz3 INTERFACE
  $<BUILD_INTERFACE:${Z3_BUILD_INCLUDE_DIR}>
)

# This is currently only for the OpenMP flags. It needs to be set
# via `target_link_libraries()` rather than `z3_append_linker_flag_list_to_target()`
# because when building the `libz3` as a static library when the target is exported
# the link dependencies need to be exported too.
foreach (flag_name ${Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS})
  target_link_libraries(libz3 PRIVATE ${flag_name})
endforeach()

# Declare which header file are the public header files of libz3
# these will automatically installed when the libz3 target is installed
set (libz3_public_headers
  z3_algebraic.h
  z3_api.h
  z3_ast_containers.h
  z3_fixedpoint.h
  z3_fpa.h
  z3.h
  c++/z3++.h
  z3_macros.h
  z3_optimization.h
  z3_polynomial.h
  z3_rcf.h
  z3_v1.h
  z3_spacer.h
)
foreach (header ${libz3_public_headers})
  set_property(TARGET libz3 APPEND PROPERTY
    PUBLIC_HEADER "${PROJECT_SOURCE_DIR}/src/api/${header}")
endforeach()
set_property(TARGET libz3 APPEND PROPERTY
    PUBLIC_HEADER "${CMAKE_CURRENT_BINARY_DIR}/util/z3_version.h")

install(TARGETS libz3
  EXPORT Z3_EXPORTED_TARGETS
  LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}"
  ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}" # On Windows this installs ``libz3.lib`` which CMake calls the "corresponding import library". Do we want this installed?
  RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}" # For Windows. DLLs are runtime targets for CMake
  PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}"
)

if (MSVC)
  # Handle settings dll exports when using MSVC
  # FIXME: This seems unnecessarily complicated but I'm doing
  # this because this is what the python build system does.
  # CMake has a much more elegant (see ``GenerateExportHeader.cmake``)
  # way of handling this.
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
  add_custom_target(libz3_extra_depends
    DEPENDS "${dll_module_exports_file}"
  )
  add_dependencies(libz3 libz3_extra_depends)
  z3_append_linker_flag_list_to_target(libz3 "/DEF:${dll_module_exports_file}")
endif()

################################################################################
# Z3 executable
################################################################################
cmake_dependent_option(Z3_BUILD_EXECUTABLE
    "Build the z3 executable" ON
    "CMAKE_SOURCE_DIR STREQUAL PROJECT_SOURCE_DIR;Z3_BUILD_LIBZ3_CORE" OFF)

if (Z3_BUILD_EXECUTABLE)
    add_subdirectory(shell)
endif()

################################################################################
# z3-test
################################################################################

cmake_dependent_option(Z3_BUILD_TEST_EXECUTABLES
    "Build test executables" ON
    "CMAKE_SOURCE_DIR STREQUAL PROJECT_SOURCE_DIR;Z3_BUILD_LIBZ3_CORE" OFF)


if (Z3_BUILD_TEST_EXECUTABLES)
    add_subdirectory(test)
endif()

################################################################################
# .NET bindings
################################################################################
option(Z3_BUILD_DOTNET_BINDINGS "Build .NET bindings for Z3" OFF)
if (Z3_BUILD_DOTNET_BINDINGS)
  if (NOT Z3_BUILD_LIBZ3_SHARED)
    message(FATAL_ERROR "The .NET bindings will not work with a static libz3. "
      "You either need to disable Z3_BUILD_DOTNET_BINDINGS or enable Z3_BUILD_LIBZ3_SHARED")
  endif()
  add_subdirectory(api/dotnet)
endif()

################################################################################
# Java bindings
################################################################################
option(Z3_BUILD_JAVA_BINDINGS "Build Java bindings for Z3" OFF)
if (Z3_BUILD_JAVA_BINDINGS)
  if (NOT Z3_BUILD_LIBZ3_SHARED)
    message(FATAL_ERROR "The Java bindings will not work with a static libz3. "
      "You either need to disable Z3_BUILD_JAVA_BINDINGS or enable Z3_BUILD_LIBZ3_SHARED")
  endif()
  add_subdirectory(api/java)
endif()

################################################################################
# OCaml bindings
################################################################################
option(Z3_BUILD_OCAML_BINDINGS "Build OCaml bindings for Z3" OFF)
if (Z3_BUILD_OCAML_BINDINGS)
  if (NOT Z3_BUILD_LIBZ3_SHARED)
    message(FATAL_ERROR "The OCaml bindings will not work with a static libz3. "
      "You either need to disable Z3_BUILD_OCAML_BINDINGS or enable Z3_BUILD_LIBZ3_SHARED")
  endif()
  add_subdirectory(api/ml)
endif()

################################################################################
# Julia bindings
################################################################################
option(Z3_BUILD_JULIA_BINDINGS "Build Julia bindings for Z3" OFF)
if (Z3_BUILD_JULIA_BINDINGS)
  if (NOT Z3_BUILD_LIBZ3_SHARED)
    message(FATAL_ERROR "The Julia bindings will not work with a static libz3."
      "You either need to disable Z3_BUILD_JULIA_BINDINGS or enable Z3_BUILD_LIBZ3_SHARED")
  endif()
  add_subdirectory(api/julia)
endif()

################################################################################
# Go bindings
################################################################################
option(Z3_BUILD_GO_BINDINGS "Build Go bindings for Z3" OFF)
if (Z3_BUILD_GO_BINDINGS)
  if (NOT Z3_BUILD_LIBZ3_SHARED)
    message(FATAL_ERROR "The Go bindings will not work with a static libz3. "
      "You either need to disable Z3_BUILD_GO_BINDINGS or enable Z3_BUILD_LIBZ3_SHARED")
  endif()
  add_subdirectory(api/go)
endif()

# TODO: Implement support for other bindigns
