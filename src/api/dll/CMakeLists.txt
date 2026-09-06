set(api_dll_deps api extra_cmds sat)
z3_add_component(api_dll
  SOURCES
    dll.cpp
  COMPONENT_DEPENDENCIES
    ${api_dll_deps}
)
z3_generate_registration(api_dll)
