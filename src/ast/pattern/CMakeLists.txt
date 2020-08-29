# If this code for adding the rule to generate the database file is ever needed
# for other components then we should refactor this code into
# z3_add_component()
if (EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/database.h")
  message(FATAL_ERROR "The generated file \"${CMAKE_CURRENT_SOURCE_DIR}/database.h\""
          ${z3_polluted_tree_msg})
endif()

add_custom_command(OUTPUT "database.h"
  COMMAND "${PYTHON_EXECUTABLE}"
          "${PROJECT_SOURCE_DIR}/scripts/mk_pat_db.py"
          "${CMAKE_CURRENT_SOURCE_DIR}/database.smt2"
          "${CMAKE_CURRENT_BINARY_DIR}/database.h"
  MAIN_DEPENDENCY "${CMAKE_CURRENT_SOURCE_DIR}/database.smt2"
  DEPENDS "${PROJECT_SOURCE_DIR}/scripts/mk_pat_db.py"
          ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
  COMMENT "Generating \"database.h\""
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
  VERBATIM
)

z3_add_component(pattern
  SOURCES
    expr_pattern_match.cpp
    pattern_inference.cpp
    # Let CMake know this target depends on this generated
    # header file
    ${CMAKE_CURRENT_BINARY_DIR}/database.h
  COMPONENT_DEPENDENCIES
    normal_forms
    rewriter
    smt2parser
)
