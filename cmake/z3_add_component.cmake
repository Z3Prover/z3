#[============================================================================[

z3_add_component(component_name
  SOURCES source1 [source2...]
  [COMPONENT_DEPENDENCIES component1 [component2...]]
)

Declares a Z3 component (an OBJECT library) with target name `component_name`
and links it to libz3.

The `SOURCES` argument lists the source files and headers (including any
that are generated at build or configure time) of the component.

The `COMPONENT_DEPENDENCIES` argument accepts a list of components that
`component_name` depends on. These components get linked directly to
consumers of `component_name` so that object files propagate, too.

#]============================================================================]
function(z3_add_component component_name)
  cmake_parse_arguments(PARSE_ARGV 1 Z3_MOD
      "" "" "SOURCES;COMPONENT_DEPENDENCIES")

  message(VERBOSE "Adding component ${component_name}")

  add_library(${component_name} OBJECT ${Z3_MOD_SOURCES})
  set_target_properties(${component_name} PROPERTIES
      # Position independent code needed in shared libraries
      POSITION_INDEPENDENT_CODE ON
      # Ensure that named components are always treated as CMake target names.
      # This ensures that a misspelled component name gets diagnosed, rather
      # than silently converted to a -l flag.
      LINK_LIBRARIES_ONLY_TARGETS ON
      # Symbol visibility
      CXX_VISIBILITY_PRESET hidden
      VISIBILITY_INLINES_HIDDEN ON
  )

  target_link_libraries(${component_name} PRIVATE z3_common ${Z3_MOD_COMPONENT_DEPENDENCIES})

  # Object files propagate only from direct OBJECT library dependencies.
  # Inject component dependencies into final consumers' direct link sets so
  # CMake carries the complete object closure without manual expansion.
  set_property(TARGET ${component_name} APPEND PROPERTY
      INTERFACE_LINK_LIBRARIES_DIRECT ${Z3_MOD_COMPONENT_DEPENDENCIES})

  target_link_libraries(libz3 PRIVATE "$<BUILD_LOCAL_INTERFACE:${component_name}>")
endfunction()
