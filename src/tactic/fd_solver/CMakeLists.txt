z3_add_component(fd_solver
  SOURCES
    fd_simplifier.cpp
    fd_solver.cpp
    smtfd_solver.cpp
  COMPONENT_DEPENDENCIES
    sat_solver
)
