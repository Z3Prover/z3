z3_add_component(proto_model
  SOURCES
    proto_model.cpp
  COMPONENT_DEPENDENCIES
    model
    rewriter
    smt_params
)
