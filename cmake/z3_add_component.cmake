include(CMakeParseArguments)
define_property(GLOBAL PROPERTY Z3_LIBZ3_COMPONENTS
                BRIEF_DOCS "List of Z3 components to use in libz3"
                FULL_DOCS "List of Z3 components to use in libz3")

function(z3_expand_dependencies output_var)
  if (ARGC LESS 2)
    message(FATAL_ERROR "Invalid number of arguments")
  endif()
  # Remaining args should be component names
  set(_expanded_deps ${ARGN})
  set(_old_number_of_deps 0)
  list(LENGTH _expanded_deps _number_of_deps)
  while (_number_of_deps GREATER _old_number_of_deps)
    set(_old_number_of_deps "${_number_of_deps}")
    # Loop over the known dependencies and retrieve their dependencies
    set(_old_expanded_deps ${_expanded_deps})
    foreach (dependency ${_old_expanded_deps})
      get_property(_depdeps GLOBAL PROPERTY Z3_${dependency}_DEPS)
      list(APPEND _expanded_deps ${_depdeps})
      unset(_depdeps)
    endforeach()
    list(REMOVE_DUPLICATES _expanded_deps)
    list(LENGTH _expanded_deps _number_of_deps)
  endwhile()
  set(${output_var} ${_expanded_deps} PARENT_SCOPE)
endfunction()

function(z3_add_component_dependencies_to_target target_name)
  if (ARGC LESS 2)
    message(FATAL_ERROR "Invalid number of arguments")
  endif()
  if (NOT (TARGET ${target_name}))
    message(FATAL_ERROR "Target \"${target_name}\" does not exist")
  endif()
  # Remaining args should be component names
  set(_expanded_deps ${ARGN})
  foreach (dependency ${_expanded_deps})
    # Ensure this component's dependencies are built before this component.
    # This is important because we might need the generated header files in
    # other components.
    add_dependencies(${target_name} ${dependency})
  endforeach()
endfunction()

# z3_add_component(component_name
#   [NOT_LIBZ3_COMPONENT]
#   SOURCES source1 [source2...]
#   [COMPONENT_DEPENDENCIES component1 [component2...]]
#   [PYG_FILES pygfile1 [pygfile2...]]
#   [TACTIC_HEADERS header_file1 [header_file2...]]
#   [EXTRA_REGISTER_MODULE_HEADERS header_file1 [header_file2...]]
#   [MEMORY_INIT_FINALIZER_HEADERS header_file1 [header_file2...]]
# )
#
# Declares a Z3 component (as a CMake "object library") with target name
# ``component_name``.
#
# The option ``NOT_LIBZ3_COMPONENT`` declares that the
# component should not be included in libz3. If this is not specified
# the component will be included in libz3.
#
# The mandatory ``SOURCES`` keyword should be followed by the source files
# (including any files generated at build or configure time) that are should be
# included in the component. It is not necessary to list header files here as
# CMake infers header file dependencies unless that header file is generated at
# build time.
#
# The optional ``COMPONENT_DEPENDENCIES`` keyword should be followed by a list of
# components that ``component_name`` should depend on. The components listed here
# must have already been declared using ``z3_add_component()``. Listing components
# here causes them to be built before ``component_name``. It also currently causes
# the include directories used by the transistive closure of the dependencies
# to be added to the list of include directories used to build ``component_name``.
#
# The optional ``PYG_FILES`` keyword should be followed by a list of one or
# more ``<NAME>.pyg`` files that should used to be generate
# ``<NAME>_params.hpp`` header files used by the ``component_name``.
# This generated file will automatically be scanned for the register module
# declarations (i.e. ``REG_PARAMS()``, ``REG_MODULE_PARAMS()``, and
# ``REG_MODULE_DESCRIPTION()``).
#
# The optional ``TACTIC_HEADERS`` keyword should be followed by a list of one or
# more header files that declare a tactic and/or a probe that is part of this
# component (see ``ADD_TACTIC()`` and ``ADD_PROBE()``).
#
# The optional ``EXTRA_REGISTER_MODULE_HEADERS`` keyword should be followed by a list
# of one or more header files that contain module registration declarations.
# NOTE: The header files generated from ``.pyg`` files don't need to be included.
#
# The optional ``MEMORY_INIT_FINALIZER_HEADERS`` keyword should be followed by a list
# of one or more header files that contain memory initializer/finalizer declarations
# (i.e. ``ADD_INITIALIZER()`` or ``ADD_FINALIZER()``).
macro(z3_add_component component_name)
  CMAKE_PARSE_ARGUMENTS("Z3_MOD"
    "NOT_LIBZ3_COMPONENT"
    ""
    "SOURCES;COMPONENT_DEPENDENCIES;PYG_FILES;TACTIC_HEADERS;EXTRA_REGISTER_MODULE_HEADERS;MEMORY_INIT_FINALIZER_HEADERS" ${ARGN})
  message(STATUS "Adding component ${component_name}")
  # Note: We don't check the sources exist here because
  # they might be generated files that don't exist yet.

  set(_list_generated_headers "")
  set_property(GLOBAL PROPERTY Z3_${component_name}_REGISTER_MODULE_HEADERS "")
  foreach (pyg_file ${Z3_MOD_PYG_FILES})
    set(_full_pyg_file_path "${CMAKE_CURRENT_SOURCE_DIR}/${pyg_file}")
    if (NOT (EXISTS "${_full_pyg_file_path}"))
      message(FATAL_ERROR "\"${_full_pyg_file_path}\" does not exist")
    endif()
    string(REPLACE ".pyg" ".hpp" _output_file "${pyg_file}")
    if (EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${_output_file}")
      message(FATAL_ERROR "\"${CMAKE_CURRENT_SOURCE_DIR}/${_output_file}\" "
        ${z3_polluted_tree_msg}
      )
    endif()
    set(_full_output_file_path "${CMAKE_CURRENT_BINARY_DIR}/${_output_file}")
    message(STATUS "Adding rule to generate \"${_output_file}\"")
    add_custom_command(OUTPUT "${_output_file}"
      COMMAND "${PYTHON_EXECUTABLE}" "${PROJECT_SOURCE_DIR}/scripts/pyg2hpp.py" "${_full_pyg_file_path}" "${CMAKE_CURRENT_BINARY_DIR}"
      MAIN_DEPENDENCY "${_full_pyg_file_path}"
      DEPENDS "${PROJECT_SOURCE_DIR}/scripts/pyg2hpp.py"
              ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
      COMMENT "Generating \"${_full_output_file_path}\" from \"${pyg_file}\""
      WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
      ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
      VERBATIM
    )
    list(APPEND _list_generated_headers "${_full_output_file_path}")

    # FIXME: This implicit dependency of a generated file depending on
    # generated files was inherited from the old build system.

    # Typically generated headers contain `REG_PARAMS()`, `REG_MODULE_PARAMS()`
    # and `REG_MODULE_DESCRIPTION()` declarations so add to the list of
    # header files to scan.
    set_property(GLOBAL
      APPEND
      PROPERTY Z3_${component_name}_REGISTER_MODULE_HEADERS
      "${_full_output_file_path}"
    )
  endforeach()
  unset(_full_include_dir_path)
  unset(_full_output_file_path)
  unset(_output_file)

  # Add tactic/probe headers to global property
  set_property(GLOBAL PROPERTY Z3_${component_name}_TACTIC_HEADERS "")
  foreach (tactic_header ${Z3_MOD_TACTIC_HEADERS})
    set(_full_tactic_header_file_path "${CMAKE_CURRENT_SOURCE_DIR}/${tactic_header}")
    if (NOT (EXISTS "${_full_tactic_header_file_path}"))
      message(FATAL_ERROR "\"${_full_tactic_header_file_path}\" does not exist")
    endif()
    set_property(GLOBAL
      APPEND
      PROPERTY Z3_${component_name}_TACTIC_HEADERS
      "${_full_tactic_header_file_path}"
    )
  endforeach()
  unset(_full_tactic_header_file_path)

  # Add additional register module headers
  foreach (extra_register_module_header ${Z3_MOD_EXTRA_REGISTER_MODULE_HEADERS})
    set(_full_extra_register_module_header_path
      "${CMAKE_CURRENT_SOURCE_DIR}/${extra_register_module_header}"
    )
    if (NOT (EXISTS "${_full_extra_register_module_header_path}"))
      message(FATAL_ERROR "\"${_full_extra_register_module_header_path}\" does not exist")
    endif()
    set_property(GLOBAL
      APPEND
      PROPERTY Z3_${component_name}_REGISTER_MODULE_HEADERS
      "${_full_extra_register_module_header_path}"
    )
  endforeach()
  unset(_full_extra_register_module_header)

  # Add memory initializer/finalizer headers to global property
  set_property(GLOBAL PROPERTY Z3_${component_name}_MEM_INIT_FINALIZER_HEADERS "")
  foreach (memory_init_finalizer_header ${Z3_MOD_MEMORY_INIT_FINALIZER_HEADERS})
    set(_full_memory_init_finalizer_header_path
      "${CMAKE_CURRENT_SOURCE_DIR}/${memory_init_finalizer_header}")
    if (NOT (EXISTS "${_full_memory_init_finalizer_header_path}"))
      message(FATAL_ERROR "\"${_full_memory_init_finalizer_header_path}\" does not exist")
    endif()
    set_property(GLOBAL
      APPEND
      PROPERTY Z3_${component_name}_MEM_INIT_FINALIZER_HEADERS
      "${_full_memory_init_finalizer_header_path}"
    )
  endforeach()
  unset(_full_memory_init_finalizer_header_path)

  # Using "object" libraries here means we have a convenient
  # name to refer to a component in CMake but we don't actually
  # create a static/library from them. This allows us to easily
  # build a static or dynamic library from the object libraries
  # on all platforms. Is this added flexibility worth the linking
  # overhead it adds?
  add_library(${component_name} OBJECT ${Z3_MOD_SOURCES} ${_list_generated_headers})
  unset(_list_generated_headers)
  # Add definitions
  foreach (define ${Z3_COMPONENT_CXX_DEFINES})
    target_compile_definitions(${component_name} PRIVATE ${define})
  endforeach()
  # Add compiler flags
  foreach (flag ${Z3_COMPONENT_CXX_FLAGS})
    target_compile_options(${component_name} PRIVATE ${flag})
  endforeach()

  # It's unfortunate that we have to manage dependencies ourselves.
  #
  # If we weren't building "object" libraries we could use
  # ```
  # target_link_libraries(${component_name} INTERFACE ${Z3_MOD_COMPONENT_DEPENDENCIES})
  # ```
  # but we can't do that with "object" libraries.

  set_property(GLOBAL PROPERTY Z3_${component_name}_DEPS "")
  # Record this component's dependencies
  foreach (dependency ${Z3_MOD_COMPONENT_DEPENDENCIES})
    if (NOT (TARGET ${dependency}))
      message(FATAL_ERROR "Component \"${component_name}\" depends on a non existent component \"${dependency}\"")
    endif()
    set_property(GLOBAL APPEND PROPERTY Z3_${component_name}_DEPS "${dependency}")
  endforeach()

  # Determine all the components that this component depends on
  set(_expanded_deps "")
  if (DEFINED Z3_MOD_COMPONENT_DEPENDENCIES)
    z3_expand_dependencies(_expanded_deps ${Z3_MOD_COMPONENT_DEPENDENCIES})
    z3_add_component_dependencies_to_target(${component_name} ${_expanded_deps})
  endif()
  #message(STATUS "Component \"${component_name}\" has the following dependencies ${_expanded_deps}")

  # Add any extra include directories
  foreach (extra_include ${Z3_COMPONENT_EXTRA_INCLUDE_DIRS})
    target_include_directories(${component_name} PRIVATE "${extra_include}")
  endforeach()

  if (NOT Z3_MOD_NOT_LIBZ3_COMPONENT)
    # Add this component to the global list of Z3 components for libz3
    set_property(GLOBAL APPEND PROPERTY Z3_LIBZ3_COMPONENTS ${component_name})
  endif()
endmacro()

macro(z3_add_install_tactic_rule)
  # Arguments should be component names to use
  if (ARGC LESS 1)
    message(FATAL_ERROR "There should be at least one component")
  endif()
  if (EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/install_tactic.cpp")
    message(FATAL_ERROR "\"${CMAKE_CURRENT_SOURCE_DIR}/install_tactic.cpp\""
            ${z3_polluted_tree_msg}
    )
  endif()
  z3_expand_dependencies(_expanded_components ${ARGN})

  # Get header files that declare tactics/probes
  set(_tactic_header_files "")
  foreach (dependency ${_expanded_components})
    get_property(_component_tactic_header_files
      GLOBAL
      PROPERTY Z3_${dependency}_TACTIC_HEADERS
    )
    list(APPEND _tactic_header_files "${_component_tactic_header_files}")
  endforeach()
  unset(_component_tactic_header_files)

  string(REPLACE ";" "\n" _tactic_header_files "${_tactic_header_files}")
  file(WRITE "${CMAKE_CURRENT_BINARY_DIR}/install_tactic.deps" ${_tactic_header_files})
  add_custom_command(OUTPUT "install_tactic.cpp"
    COMMAND "${PYTHON_EXECUTABLE}"
    "${PROJECT_SOURCE_DIR}/scripts/mk_install_tactic_cpp.py"
    "${CMAKE_CURRENT_BINARY_DIR}"
    "${CMAKE_CURRENT_BINARY_DIR}/install_tactic.deps"
    DEPENDS "${PROJECT_SOURCE_DIR}/scripts/mk_install_tactic_cpp.py"
            ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
            "${CMAKE_CURRENT_BINARY_DIR}/install_tactic.deps"
    COMMENT "Generating \"${CMAKE_CURRENT_BINARY_DIR}/install_tactic.cpp\""
    ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
    VERBATIM
  )
  unset(_expanded_components)
  unset(_tactic_header_files)
endmacro()

macro(z3_add_memory_initializer_rule)
  # Arguments should be component names to use
  if (ARGC LESS 1)
    message(FATAL_ERROR "There should be at least one component")
  endif()
  if (EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/mem_initializer.cpp")
    message(FATAL_ERROR "\"${CMAKE_CURRENT_SOURCE_DIR}/mem_initializer.cpp\""
            ${z3_polluted_tree_msg}
    )
  endif()
  z3_expand_dependencies(_expanded_components ${ARGN})

  # Get header files that declare initializers and finalizers
  set(_mem_init_finalize_headers "")
  foreach (dependency ${_expanded_components})
    get_property(_dep_mem_init_finalize_headers
      GLOBAL
      PROPERTY Z3_${dependency}_MEM_INIT_FINALIZER_HEADERS
    )
    list(APPEND _mem_init_finalize_headers ${_dep_mem_init_finalize_headers})
  endforeach()

  add_custom_command(OUTPUT "mem_initializer.cpp"
    COMMAND "${PYTHON_EXECUTABLE}"
    "${PROJECT_SOURCE_DIR}/scripts/mk_mem_initializer_cpp.py"
    "${CMAKE_CURRENT_BINARY_DIR}"
    ${_mem_init_finalize_headers}
    DEPENDS "${PROJECT_SOURCE_DIR}/scripts/mk_mem_initializer_cpp.py"
            ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
            ${_mem_init_finalize_headers}
    COMMENT "Generating \"${CMAKE_CURRENT_BINARY_DIR}/mem_initializer.cpp\""
    ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
    VERBATIM
  )
  unset(_mem_init_finalize_headers)
  unset(_expanded_components)
endmacro()

macro(z3_add_gparams_register_modules_rule)
  # Arguments should be component names to use
  if (ARGC LESS 1)
    message(FATAL_ERROR "There should be at least one component")
  endif()
  if (EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/gparams_register_modules.cpp")
    message(FATAL_ERROR "\"${CMAKE_CURRENT_SOURCE_DIR}/gparams_register_modules.cpp\""
            ${z3_polluted_tree_msg}
    )
  endif()
  z3_expand_dependencies(_expanded_components ${ARGN})

  # Get the list of header files to parse
  set(_register_module_header_files "")
  foreach (dependency ${_expanded_components})
    get_property(_component_register_module_header_files GLOBAL PROPERTY Z3_${dependency}_REGISTER_MODULE_HEADERS)
    list(APPEND _register_module_header_files ${_component_register_module_header_files})
  endforeach()
  unset(_component_register_module_header_files)

  add_custom_command(OUTPUT "gparams_register_modules.cpp"
    COMMAND "${PYTHON_EXECUTABLE}"
    "${PROJECT_SOURCE_DIR}/scripts/mk_gparams_register_modules_cpp.py"
    "${CMAKE_CURRENT_BINARY_DIR}"
    ${_register_module_header_files}
    DEPENDS "${PROJECT_SOURCE_DIR}/scripts/mk_gparams_register_modules_cpp.py"
            ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
            ${_register_module_header_files}
    COMMENT "Generating \"${CMAKE_CURRENT_BINARY_DIR}/gparams_register_modules.cpp\""
    ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
    VERBATIM
  )
  unset(_expanded_components)
  unset(_register_module_header_files)
endmacro()
