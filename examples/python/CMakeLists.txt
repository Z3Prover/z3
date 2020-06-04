set(python_example_files
  all_interval_series.py
  complex/complex.py
  example.py
  hamiltonian/hamiltonian.py
  mus/marco.py
  mus/mss.py
  socrates.py
  visitor.py
)

set(z3py_bindings_build_dest "${PROJECT_BINARY_DIR}/python")

set(build_z3_python_examples_target_depends "")
foreach (example_file ${python_example_files})
  get_filename_component(example_file_name "${example_file}" NAME)
  add_custom_command(OUTPUT "${z3py_bindings_build_dest}/${example_file_name}"
    COMMAND "${CMAKE_COMMAND}" "-E" "copy"
      "${CMAKE_CURRENT_SOURCE_DIR}/${example_file}"
      # We flatten the hierarchy so that all python files have
      # the `z3` directory in their directory so that their import
      # statements "just work".
      "${z3py_bindings_build_dest}/${example_file_name}"
    DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/${example_file}"
    COMMENT "Copying \"${example_file}\" to ${z3py_bindings_build_dest}/${example_file_name}"
  )
  list(APPEND build_z3_python_examples_target_depends "${z3py_bindings_build_dest}/${example_file_name}")
endforeach()

add_custom_target(build_z3_python_examples
  ALL
  DEPENDS
    ${build_z3_python_examples_target_depends}
)
