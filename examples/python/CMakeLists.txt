set(python_example_files
  example.py
  visitor.py
)

set(z3py_bindings_build_dest "${CMAKE_BINARY_DIR}/python")

set(build_z3_python_examples_target_depends "")
foreach (example_file ${python_example_files})
  add_custom_command(OUTPUT "${z3py_bindings_build_dest}/${example_file}"
    COMMAND "${CMAKE_COMMAND}" "-E" "copy"
      "${CMAKE_CURRENT_SOURCE_DIR}/${example_file}"
      "${z3py_bindings_build_dest}/${example_file}"
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
