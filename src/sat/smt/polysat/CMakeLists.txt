z3_add_component(polysat
  SOURCES
    polysat_assignment.cpp
    polysat_constraints.cpp
    polysat_core.cpp
    polysat_fi.cpp
    polysat_ule.cpp
    polysat_umul_ovfl.cpp
    polysat_viable.cpp
  COMPONENT_DEPENDENCIES
    util
    dd
    smt_params
)

