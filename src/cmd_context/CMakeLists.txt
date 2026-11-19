# This translation unit pulls in every registration (see z3_add_component). It
# is generated at build time from the REGISTRATION_HEADERS of all components,
# which z3_add_component collects in a libz3 file set.
set(Z3_REGISTRATIONS_SOURCE "${CMAKE_CURRENT_BINARY_DIR}/z3_registrations.cpp")
set(Z3_REGISTRATION_HEADERS "$<TARGET_PROPERTY:libz3,HEADER_SET_registrations>")
# The header list is too long to pass reliably on the command line (e.g. NMake),
# so hand it to the generator through a file.
set(Z3_REGISTRATION_HEADERS_LIST "${CMAKE_CURRENT_BINARY_DIR}/z3_registration_headers.txt")
file(GENERATE
  OUTPUT "${Z3_REGISTRATION_HEADERS_LIST}"
  CONTENT "$<JOIN:${Z3_REGISTRATION_HEADERS},\n>\n"
)
add_custom_command(
  OUTPUT "${Z3_REGISTRATIONS_SOURCE}"
  COMMAND "${CMAKE_COMMAND}"
    "-DHEADERS_FILE=${Z3_REGISTRATION_HEADERS_LIST}"
    "-DSRC_DIR=${PROJECT_SOURCE_DIR}/src"
    "-DOUTPUT=${Z3_REGISTRATIONS_SOURCE}"
    -P "${PROJECT_SOURCE_DIR}/cmake/z3_generate_registrations.cmake"
  DEPENDS
    "${PROJECT_SOURCE_DIR}/cmake/z3_generate_registrations.cmake"
    "${Z3_REGISTRATION_HEADERS_LIST}"
    "${Z3_REGISTRATION_HEADERS}"
  COMMENT "Generating tactic/probe/simplifier registrations"
  VERBATIM
)

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
    "${Z3_REGISTRATIONS_SOURCE}"
  COMPONENT_DEPENDENCIES
    rewriter
    solver
    params
)

add_subdirectory(extra_cmds)
