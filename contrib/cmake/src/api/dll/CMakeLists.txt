set(api_dll_deps api extra_cmds sat)
z3_add_component(api_dll
  SOURCES
    dll.cpp
    "${CMAKE_CURRENT_BINARY_DIR}/gparams_register_modules.cpp"
    "${CMAKE_CURRENT_BINARY_DIR}/install_tactic.cpp"
    "${CMAKE_CURRENT_BINARY_DIR}/mem_initializer.cpp"
  COMPONENT_DEPENDENCIES
    ${api_dll_deps}
)
z3_add_install_tactic_rule(${api_dll_deps})
z3_add_memory_initializer_rule(${api_dll_deps})
z3_add_gparams_register_modules_rule(${api_dll_deps})
