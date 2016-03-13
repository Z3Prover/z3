set(generated_files
  api_commands.cpp
  api_log_macros.cpp
  api_log_macros.h
)

# Sanity check
foreach (gen_file ${generated_files})
  if (EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${gen_file}")
    message(FATAL_ERROR "\"${CMAKE_CURRENT_SOURCE_DIR}/${gen_files}\""
            ${z3_polluted_tree_msg})
  endif()
endforeach()

set(full_path_generated_files "")
foreach (gen_file ${generated_files})
  list(APPEND full_path_generated_files "${CMAKE_CURRENT_BINARY_DIR}/${gen_file}")
endforeach()

add_custom_command(OUTPUT ${generated_files}
  COMMAND "${PYTHON_EXECUTABLE}"
  "${CMAKE_SOURCE_DIR}/scripts/update_api.py"
  ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
  "--api_output_dir"
  "${CMAKE_CURRENT_BINARY_DIR}"
  DEPENDS "${CMAKE_SOURCE_DIR}/scripts/update_api.py"
          ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
          ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
          # FIXME: When update_api.py no longer uses ``mk_util`` drop this dependency
          "${CMAKE_SOURCE_DIR}/scripts/mk_util.py"
  COMMENT "Generating ${generated_files}"
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
  VERBATIM
)

z3_add_component(api
  SOURCES
    api_algebraic.cpp
    api_arith.cpp
    api_array.cpp
    api_ast.cpp
    api_ast_map.cpp
    api_ast_vector.cpp
    api_bv.cpp
    api_config_params.cpp
    api_context.cpp
    api_datalog.cpp
    api_datatype.cpp
    api_fpa.cpp
    api_goal.cpp
    api_interp.cpp
    api_log.cpp
    api_model.cpp
    api_numeral.cpp
    api_opt.cpp
    api_params.cpp
    api_parsers.cpp
    api_pb.cpp
    api_polynomial.cpp
    api_quant.cpp
    api_rcf.cpp
    api_seq.cpp
    api_solver.cpp
    api_stats.cpp
    api_tactic.cpp
    z3_replayer.cpp
    ${full_path_generated_files}
  COMPONENT_DEPENDENCIES
    interp
    opt
    portfolio
    realclosure
    smtparser
)
