define_property(TARGET PROPERTY INTERFACE_Z3_REGISTER_MODULE_HEADERS
                BRIEF_DOCS "Headers containing Z3 module registrations"
                FULL_DOCS "Headers scanned to generate parameter registration code")
define_property(TARGET PROPERTY INTERFACE_Z3_TACTIC_HEADERS
                BRIEF_DOCS "Headers containing Z3 tactic registrations"
                FULL_DOCS "Headers scanned to generate tactic installation code")
define_property(TARGET PROPERTY INTERFACE_Z3_MEM_INIT_FINALIZER_HEADERS
                BRIEF_DOCS "Headers containing Z3 memory hooks"
                FULL_DOCS "Headers scanned to generate memory initialization code")

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
# components that ``component_name`` should depend on. Listing components here
# causes them to be built before ``component_name`` and propagates their usage
# requirements.
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
function(z3_add_component component_name)
  cmake_parse_arguments(PARSE_ARGV 1 Z3_MOD
    "NOT_LIBZ3_COMPONENT"
    ""
    "SOURCES;COMPONENT_DEPENDENCIES;PYG_FILES;TACTIC_HEADERS;EXTRA_REGISTER_MODULE_HEADERS;MEMORY_INIT_FINALIZER_HEADERS")
  message(STATUS "Adding component ${component_name}")
  # Note: We don't check the sources exist here because
  # they might be generated files that don't exist yet.

  set(_list_generated_headers "")
  set(_register_module_headers "")
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
      COMMAND "${Python3_EXECUTABLE}" "${PROJECT_SOURCE_DIR}/scripts/pyg2hpp.py" "${_full_pyg_file_path}" "${CMAKE_CURRENT_BINARY_DIR}"
      MAIN_DEPENDENCY "${_full_pyg_file_path}"
      DEPENDS "${PROJECT_SOURCE_DIR}/scripts/pyg2hpp.py"
              ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
      COMMENT "Generating \"${_full_output_file_path}\" from \"${pyg_file}\""
      WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
      USES_TERMINAL
      VERBATIM
    )
    list(APPEND _list_generated_headers "${_full_output_file_path}")

    # FIXME: This implicit dependency of a generated file depending on
    # generated files was inherited from the old build system.

    # Typically generated headers contain `REG_PARAMS()`, `REG_MODULE_PARAMS()`
    # and `REG_MODULE_DESCRIPTION()` declarations so add to the list of
    # header files to scan.
    list(APPEND _register_module_headers "${_full_output_file_path}")
  endforeach()
  # Resolve tactic/probe headers.
  set(_tactic_headers "")
  foreach (tactic_header ${Z3_MOD_TACTIC_HEADERS})
    set(_full_tactic_header_file_path "${CMAKE_CURRENT_SOURCE_DIR}/${tactic_header}")
    if (NOT (EXISTS "${_full_tactic_header_file_path}"))
      message(FATAL_ERROR "\"${_full_tactic_header_file_path}\" does not exist")
    endif()
    list(APPEND _tactic_headers "${_full_tactic_header_file_path}")
  endforeach()
  # Add additional register module headers
  foreach (extra_register_module_header ${Z3_MOD_EXTRA_REGISTER_MODULE_HEADERS})
    set(_full_extra_register_module_header_path
      "${CMAKE_CURRENT_SOURCE_DIR}/${extra_register_module_header}"
    )
    if (NOT (EXISTS "${_full_extra_register_module_header_path}"))
      message(FATAL_ERROR "\"${_full_extra_register_module_header_path}\" does not exist")
    endif()
    list(APPEND _register_module_headers
      "${_full_extra_register_module_header_path}")
  endforeach()
  # Resolve memory initializer/finalizer headers.
  set(_mem_init_finalizer_headers "")
  foreach (memory_init_finalizer_header ${Z3_MOD_MEMORY_INIT_FINALIZER_HEADERS})
    set(_full_memory_init_finalizer_header_path
      "${CMAKE_CURRENT_SOURCE_DIR}/${memory_init_finalizer_header}")
    if (NOT (EXISTS "${_full_memory_init_finalizer_header_path}"))
      message(FATAL_ERROR "\"${_full_memory_init_finalizer_header_path}\" does not exist")
    endif()
    list(APPEND _mem_init_finalizer_headers
      "${_full_memory_init_finalizer_header_path}")
  endforeach()
  # Using "object" libraries here means we have a convenient
  # name to refer to a component in CMake but we don't actually
  # create a static/library from them. This allows us to easily
  # build a static or dynamic library from the object libraries
  # on all platforms. Is this added flexibility worth the linking
  # overhead it adds?
  add_library(${component_name} OBJECT ${Z3_MOD_SOURCES} ${_list_generated_headers})
  target_link_libraries(${component_name} PRIVATE z3_common)
  set_target_properties(${component_name} PROPERTIES
    INTERFACE_Z3_REGISTER_MODULE_HEADERS "${_register_module_headers}"
    INTERFACE_Z3_TACTIC_HEADERS "${_tactic_headers}"
    INTERFACE_Z3_MEM_INIT_FINALIZER_HEADERS "${_mem_init_finalizer_headers}"
  )
  set_target_properties(${component_name} PROPERTIES
    # Position independent code needed in shared libraries
    POSITION_INDEPENDENT_CODE ON
    # Symbol visibility
    CXX_VISIBILITY_PRESET hidden
    LINK_LIBRARIES_ONLY_TARGETS ON
    VISIBILITY_INLINES_HIDDEN ON)

  # OBJECT libraries support ordinary usage requirements and dependency
  # propagation.  Their object files are added separately to final binaries.
  if (Z3_MOD_COMPONENT_DEPENDENCIES)
    target_link_libraries(${component_name} PRIVATE
      ${Z3_MOD_COMPONENT_DEPENDENCIES})

    # Object files propagate only from direct OBJECT library dependencies.
    # Inject component dependencies into final consumers' direct link sets so
    # CMake carries the complete object closure without manual expansion.
    set_property(TARGET ${component_name} APPEND PROPERTY
      INTERFACE_LINK_LIBRARIES_DIRECT ${Z3_MOD_COMPONENT_DEPENDENCIES})
  endif()

  if (NOT Z3_MOD_NOT_LIBZ3_COMPONENT)
    target_link_libraries(libz3 PRIVATE
      "$<BUILD_LOCAL_INTERFACE:${component_name}>")
  endif()
endfunction()

function(z3_generate_registration target)
  if (NOT TARGET "${target}")
    message(FATAL_ERROR "Unknown target \"${target}\"")
  endif()

  foreach (_generated_source IN ITEMS
      install_tactic.cpp
      mem_initializer.cpp
      gparams_register_modules.cpp)
    if (EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${_generated_source}")
      message(FATAL_ERROR
        "\"${CMAKE_CURRENT_SOURCE_DIR}/${_generated_source}\""
        ${z3_polluted_tree_msg})
    endif()
  endforeach()

  # Registration metadata follows the private component link graph. Custom
  # transitive link properties include dependencies guarded by LINK_ONLY.
  set_property(TARGET "${target}" APPEND PROPERTY TRANSITIVE_LINK_PROPERTIES
    Z3_REGISTER_MODULE_HEADERS
    Z3_TACTIC_HEADERS
    Z3_MEM_INIT_FINALIZER_HEADERS)

  set(_register_module_headers
    "$<TARGET_PROPERTY:${target},Z3_REGISTER_MODULE_HEADERS>")
  set(_tactic_headers "$<TARGET_PROPERTY:${target},Z3_TACTIC_HEADERS>")
  set(_mem_init_finalizer_headers
    "$<TARGET_PROPERTY:${target},Z3_MEM_INIT_FINALIZER_HEADERS>")

  # The tactic generator takes its inputs in a file. file(GENERATE) evaluates
  # the target's transitive metadata without rewriting an unchanged deps file.
  set(_install_tactic_deps
    "${CMAKE_CURRENT_BINARY_DIR}/install_tactic.deps")
  file(GENERATE
    OUTPUT "${_install_tactic_deps}"
    CONTENT "$<JOIN:${_tactic_headers},\n>"
    TARGET "${target}")

  add_custom_command(OUTPUT
      "${CMAKE_CURRENT_BINARY_DIR}/install_tactic.cpp"
    COMMAND "${Python3_EXECUTABLE}"
      "${PROJECT_SOURCE_DIR}/scripts/mk_install_tactic_cpp.py"
      "${CMAKE_CURRENT_BINARY_DIR}"
      "${_install_tactic_deps}"
    DEPENDS "${PROJECT_SOURCE_DIR}/scripts/mk_install_tactic_cpp.py"
      ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
      "${_install_tactic_deps}"
    COMMENT "Generating \"${CMAKE_CURRENT_BINARY_DIR}/install_tactic.cpp\""
    USES_TERMINAL
    VERBATIM)

  add_custom_command(OUTPUT
      "${CMAKE_CURRENT_BINARY_DIR}/mem_initializer.cpp"
    COMMAND "${Python3_EXECUTABLE}"
      "${PROJECT_SOURCE_DIR}/scripts/mk_mem_initializer_cpp.py"
      "${CMAKE_CURRENT_BINARY_DIR}"
      "${_mem_init_finalizer_headers}"
    DEPENDS "${PROJECT_SOURCE_DIR}/scripts/mk_mem_initializer_cpp.py"
      ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
      "${_mem_init_finalizer_headers}"
    COMMENT "Generating \"${CMAKE_CURRENT_BINARY_DIR}/mem_initializer.cpp\""
    COMMAND_EXPAND_LISTS
    USES_TERMINAL
    VERBATIM)

  add_custom_command(OUTPUT
      "${CMAKE_CURRENT_BINARY_DIR}/gparams_register_modules.cpp"
    COMMAND "${Python3_EXECUTABLE}"
      "${PROJECT_SOURCE_DIR}/scripts/mk_gparams_register_modules_cpp.py"
      "${CMAKE_CURRENT_BINARY_DIR}"
      "${_register_module_headers}"
    DEPENDS "${PROJECT_SOURCE_DIR}/scripts/mk_gparams_register_modules_cpp.py"
      ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
      "${_register_module_headers}"
    COMMENT
      "Generating \"${CMAKE_CURRENT_BINARY_DIR}/gparams_register_modules.cpp\""
    COMMAND_EXPAND_LISTS
    USES_TERMINAL
    VERBATIM)

  target_sources("${target}" PRIVATE
    "${CMAKE_CURRENT_BINARY_DIR}/gparams_register_modules.cpp"
    "${CMAKE_CURRENT_BINARY_DIR}/install_tactic.cpp"
    "${CMAKE_CURRENT_BINARY_DIR}/mem_initializer.cpp")
endfunction()
