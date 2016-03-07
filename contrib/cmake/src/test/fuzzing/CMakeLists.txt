z3_add_component(fuzzing
  NOT_LIBZ3_COMPONENT # Don't put this component inside libz3
  SOURCES
    expr_delta.cpp
    expr_rand.cpp
  COMPONENT_DEPENDENCIES
    ast
)
