z3_add_component(sat_euf
  SOURCES
    euf_solver.cpp
  COMPONENT_DEPENDENCIES
    sat
    sat_smt
    euf
)
