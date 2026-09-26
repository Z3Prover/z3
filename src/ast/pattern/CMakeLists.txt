# If this code for adding the rule to generate the database file is ever needed
# for other components then we should refactor this code into
# z3_add_component()

add_custom_command(OUTPUT "database.h"
  COMMAND "${Python3_EXECUTABLE}"
          "${PROJECT_SOURCE_DIR}/scripts/mk_pat_db.py"
          "${CMAKE_CURRENT_SOURCE_DIR}/database.smt2"
          "${CMAKE_CURRENT_BINARY_DIR}/database.h"
  MAIN_DEPENDENCY "${CMAKE_CURRENT_SOURCE_DIR}/database.smt2"
  DEPENDS "${PROJECT_SOURCE_DIR}/scripts/mk_pat_db.py"
          ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
  COMMENT "Generating \"database.h\""
  VERBATIM
)

z3_add_component(pattern
  SOURCES
    expr_pattern_match.cpp
    pattern_inference.cpp
    "${CMAKE_CURRENT_BINARY_DIR}/database.h"
  COMPONENT_DEPENDENCIES
    normal_forms
    rewriter
    smt2parser
)
