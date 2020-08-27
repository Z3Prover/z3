z3_add_component(sat_smt
  SOURCES
    atom2bool_var.cpp
    sat_th.cpp
  COMPONENT_DEPENDENCIES
    sat
    ast
    euf
)

