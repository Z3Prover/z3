set (shell_object_files "")
# FIXME: z3 should really link against libz3 and not the
# individual components. Several things prevent us from
# doing this
# * The api_dll component in libz3 shouldn't be used the
#   the z3 executable.
# * The z3 executable uses symbols that are hidden in libz3

# We are only using these dependencies to enforce a build
# order. We don't use this list for actual linking.
set(shell_deps api extra_cmds opt sat)
z3_expand_dependencies(shell_expanded_deps ${shell_deps})
get_property(Z3_LIBZ3_COMPONENTS_LIST GLOBAL PROPERTY Z3_LIBZ3_COMPONENTS)
foreach (component ${Z3_LIBZ3_COMPONENTS_LIST})
  if (NOT ("${component}" STREQUAL "api_dll"))
    # We don't use the api_dll component in the Z3 executable
    list(APPEND shell_object_files $<TARGET_OBJECTS:${component}>)
  endif()
endforeach()
add_executable(shell
  datalog_frontend.cpp
  dimacs_frontend.cpp
  "${CMAKE_CURRENT_BINARY_DIR}/gparams_register_modules.cpp"
  "${CMAKE_CURRENT_BINARY_DIR}/install_tactic.cpp"
  main.cpp
  "${CMAKE_CURRENT_BINARY_DIR}/mem_initializer.cpp"
  opt_frontend.cpp
  smtlib_frontend.cpp
  z3_log_frontend.cpp
  lp_frontend.cpp
# FIXME: shell should really link against libz3 but it can't due to requiring
# use of some hidden symbols. Also libz3 has the ``api_dll`` component which
# we don't want (I think).
  ${shell_object_files}
)
z3_add_install_tactic_rule(${shell_deps})
z3_add_memory_initializer_rule(${shell_deps})
z3_add_gparams_register_modules_rule(${shell_deps})
set_target_properties(shell PROPERTIES OUTPUT_NAME z3)
target_compile_definitions(shell PRIVATE ${Z3_COMPONENT_CXX_DEFINES})
target_compile_options(shell PRIVATE ${Z3_COMPONENT_CXX_FLAGS})
target_include_directories(shell PRIVATE ${Z3_COMPONENT_EXTRA_INCLUDE_DIRS})
target_link_libraries(shell PRIVATE ${Z3_DEPENDENT_LIBS})
z3_add_component_dependencies_to_target(shell ${shell_expanded_deps})
z3_append_linker_flag_list_to_target(shell ${Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS})
install(TARGETS shell
  RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}"
)
