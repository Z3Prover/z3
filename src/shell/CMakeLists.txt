set(shell_deps api extra_cmds z3_opt sat)

add_executable(shell
  datalog_frontend.cpp
  dimacs_frontend.cpp
  drat_frontend.cpp
  main.cpp
  opt_frontend.cpp
  smtlib_frontend.cpp
  z3_log_frontend.cpp
)

set_target_properties(shell PROPERTIES
    # Position independent code needed in shared libraries
    POSITION_INDEPENDENT_CODE ON
    # Symbol visibility
    CXX_VISIBILITY_PRESET hidden
    VISIBILITY_INLINES_HIDDEN ON)

set_target_properties(shell PROPERTIES OUTPUT_NAME z3)
# The executable uses internal hidden symbols, so link the OBJECT component
# roots directly instead of going through the shared libz3 target.
target_link_libraries(shell PRIVATE
  z3_common ${shell_deps})
z3_generate_registration(shell)
install(TARGETS shell
  RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}"
)
