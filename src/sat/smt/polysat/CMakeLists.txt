z3_add_component(polysat
  SOURCES
    assignment.cpp
    constraints.cpp
    core.cpp
    fixed_bits.cpp
    forbidden_intervals.cpp
    op_constraint.cpp
    ule_constraint.cpp
    umul_ovfl_constraint.cpp
    viable.cpp
  COMPONENT_DEPENDENCIES
    util
    dd
    smt_params
)

