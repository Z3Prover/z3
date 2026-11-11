#[============================================================================[

z3_add_component(component_name
  SOURCES source1 [source2...]
  [REGISTRATION_HEADERS header1 [header2...]]
  [COMPONENT_DEPENDENCIES component1 [component2...]]
)

Declares a Z3 component (an OBJECT library) with target name `component_name`
and links it to libz3.

The `SOURCES` argument lists the source files and headers (including any
that are generated at build or configure time) of the component.

The `COMPONENT_DEPENDENCIES` argument accepts a list of components that
`component_name` depends on. These components get linked directly to
consumers of `component_name` so that object files propagate, too.

The `REGISTRATION_HEADERS` argument lists every header of the component that
self-registers a tactic, probe, or simplifier with `Z3_ADD_TACTIC`,
`Z3_ADD_PROBE` or `Z3_ADD_SIMPLIFIER`. They are added to the private header
file set `registrations` of `libz3`. A custom command on cmd_context reads
that set at build time and generates a header that includes all of them from
tactic_manager.cpp. Registration happens in an `inline` global in each header,
so without that include a static libz3 silently drops any registration whose
header is not included by some linked object file. The same command fails the
build if a header using `Z3_ADD_*` is not listed here.

#]============================================================================]
function(z3_add_component component_name)
  cmake_parse_arguments(PARSE_ARGV 1 Z3_MOD
      "" "" "SOURCES;COMPONENT_DEPENDENCIES;REGISTRATION_HEADERS")

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

  if (Z3_MOD_REGISTRATION_HEADERS)
    # Collected on libz3 (rather than on the component) so that the generator in
    # src/CMakeLists.txt can read every component's headers from one property.
    list(TRANSFORM Z3_MOD_REGISTRATION_HEADERS
         PREPEND "${CMAKE_CURRENT_SOURCE_DIR}/" OUTPUT_VARIABLE _z3_registration_abs)
    target_sources(libz3 PRIVATE
      FILE_SET registrations
      TYPE HEADERS
      BASE_DIRS "${PROJECT_SOURCE_DIR}/src"
      FILES ${_z3_registration_abs}
    )
  endif()

  target_link_libraries(${component_name} PRIVATE z3_common ${Z3_MOD_COMPONENT_DEPENDENCIES})

  # Object files propagate only from direct OBJECT library dependencies.
  # Inject component dependencies into final consumers' direct link sets so
  # CMake carries the complete object closure without manual expansion.
  set_property(TARGET ${component_name} APPEND PROPERTY
      INTERFACE_LINK_LIBRARIES_DIRECT ${Z3_MOD_COMPONENT_DEPENDENCIES})

  target_link_libraries(libz3 PRIVATE "$<BUILD_LOCAL_INTERFACE:${component_name}>")
endfunction()
