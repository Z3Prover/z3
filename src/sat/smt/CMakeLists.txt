z3_add_component(sat_smt
  SOURCES
    atom2bool_var.cpp
    ba_solver.cpp
    xor_solver.cpp
    ba_internalize.cpp
    euf_ackerman.cpp
    euf_internalize.cpp
    euf_solver.cpp
    euf_model.cpp
  COMPONENT_DEPENDENCIES
    sat
    ast
    euf
    smt_params
)

