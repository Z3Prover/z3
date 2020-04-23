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
  add_custom_command(OUTPUT "${z3py_bindings_build_dest}/${example_file}"
    COMMAND "${CMAKE_COMMAND}" "-E" "copy"
      "${CMAKE_CURRENT_SOURCE_DIR}/${example_file}"
      # We flatten the hierarchy so that all python files have
      # the `z3` directory in their directory so that their import
      # statements "just work".
      "${z3py_bindings_build_dest}/"
    DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/${example_file}"
    COMMENT "Copying \"${example_file}\" to ${z3py_bindings_build_dest}/${example_file}"
  )
  list(APPEND build_z3_python_examples_target_depends "${z3py_bindings_build_dest}/${example_file}")
endforeach()

add_custom_target(build_z3_python_examples
  ALL
  DEPENDS
    ${build_z3_python_examples_target_depends}
)
