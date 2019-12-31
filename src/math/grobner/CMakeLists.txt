z3_add_component(grobner
  SOURCES
    grobner.cpp
    pdd_solver.cpp
  COMPONENT_DEPENDENCIES
    ast
    dd
)
