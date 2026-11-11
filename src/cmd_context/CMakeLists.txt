z3_add_component(cmd_context
  SOURCES
    basic_cmds.cpp
    cmd_context.cpp
    cmd_context_to_goal.cpp
    cmd_util.cpp
    echo_tactic.cpp
    eval_cmd.cpp
    parametric_cmd.cpp
    pdecl.cpp
    simplify_cmd.cpp
    simplifier_cmds.cpp
    tactic_cmds.cpp
    tactic_manager.cpp
    tptp_frontend.cpp
  COMPONENT_DEPENDENCIES
    rewriter
    solver
    params
)

# tactic_manager.cpp includes this header to pull in every registration (see
# z3_add_component). It is generated at build time from the REGISTRATION_HEADERS
# of all components, which z3_add_component collects in a libz3 file set.
set(Z3_REGISTRATIONS_HEADER "${CMAKE_CURRENT_BINARY_DIR}/z3_registrations.h")
set(Z3_REGISTRATION_HEADERS "$<TARGET_PROPERTY:libz3,HEADER_SET_registrations>")
add_custom_command(
  OUTPUT "${Z3_REGISTRATIONS_HEADER}"
  COMMAND "${CMAKE_COMMAND}"
    "-DHEADERS=${Z3_REGISTRATION_HEADERS}"
    "-DSRC_DIR=${PROJECT_SOURCE_DIR}/src"
    "-DOUTPUT=${Z3_REGISTRATIONS_HEADER}"
    -P "${PROJECT_SOURCE_DIR}/cmake/z3_generate_registrations.cmake"
  DEPENDS
    "${PROJECT_SOURCE_DIR}/cmake/z3_generate_registrations.cmake"
    "${Z3_REGISTRATION_HEADERS}"
  COMMENT "Generating tactic/probe/simplifier registrations"
  VERBATIM
)
target_sources(cmd_context PRIVATE
  FILE_SET generated_headers
  TYPE HEADERS
  BASE_DIRS "${CMAKE_CURRENT_BINARY_DIR}"
  FILES "${Z3_REGISTRATIONS_HEADER}"
)

add_subdirectory(extra_cmds)
