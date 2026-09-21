# z3_add_component(component_name
#   [NOT_LIBZ3_COMPONENT]
#   SOURCES source1 [source2...]
#   [COMPONENT_DEPENDENCIES component1 [component2...]]
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
function(z3_add_component component_name)
  cmake_parse_arguments(PARSE_ARGV 1 Z3_MOD
    "NOT_LIBZ3_COMPONENT"
    ""
    "SOURCES;COMPONENT_DEPENDENCIES")
  message(STATUS "Adding component ${component_name}")
  # Note: We don't check the sources exist here because
  # they might be generated files that don't exist yet.

  # Using "object" libraries here means we have a convenient
  # name to refer to a component in CMake but we don't actually
  # create a static/library from them. This allows us to easily
  # build a static or dynamic library from the object libraries
  # on all platforms. Is this added flexibility worth the linking
  # overhead it adds?
  add_library(${component_name} OBJECT ${Z3_MOD_SOURCES})
  target_link_libraries(${component_name} PRIVATE z3_common)
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

