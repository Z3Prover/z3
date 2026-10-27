set(api_dll_deps api extra_cmds sat)
z3_add_component(api_dll
  SOURCES
    dll.cpp
  COMPONENT_DEPENDENCIES
    ${api_dll_deps}
)

if(EMSCRIPTEN AND NOT BUILD_SHARED_LIBS)
  # Let the JS wrapper retain registration constructors through one archive member.
  file(GLOB_RECURSE registration_headers CONFIGURE_DEPENDS "${PROJECT_SOURCE_DIR}/src/*.h")
  set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS ${registration_headers})
  set(registration_source "extern \"C\" void z3_register_builtins() {}\n")
  foreach(header IN LISTS registration_headers)
    file(STRINGS "${header}" registrations LIMIT_COUNT 1
      REGEX "^[ \t]*Z3_ADD_(TACTIC|PROBE|SIMPLIFIER)([ \t(]|$)")
    if(registrations)
      string(APPEND registration_source "#include \"${header}\"\n")
    endif()
  endforeach()
  file(GENERATE OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/wasm_register.cpp"
    CONTENT "${registration_source}")
  z3_add_component(wasm_registration
    SOURCES "${CMAKE_CURRENT_BINARY_DIR}/wasm_register.cpp"
    COMPONENT_DEPENDENCIES tactic
  )
endif()
