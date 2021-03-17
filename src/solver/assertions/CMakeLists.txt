z3_add_component(solver_assertions
  SOURCES
    asserted_formulas.cpp
  COMPONENT_DEPENDENCIES
    solver
    smt2parser
    smt_params
)
