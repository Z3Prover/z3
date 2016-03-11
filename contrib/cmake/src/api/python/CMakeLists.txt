message(STATUS "Emitting rules to build Z3 python bindings")
###############################################################################
# Add target to build python bindings for the build directory
###############################################################################
# This allows the python bindings to be used directly from the build directory
set(z3py_files
  z3.py
  z3num.py
  z3poly.py
  z3printer.py
  z3rcf.py
  z3test.py
  z3types.py
  z3util.py
)

set(z3py_bindings_build_dest "${CMAKE_BINARY_DIR}")

set(build_z3_python_bindings_target_depends "")
foreach (z3py_file ${z3py_files})
  add_custom_command(OUTPUT "${z3py_bindings_build_dest}/${z3py_file}"
    COMMAND "${CMAKE_COMMAND}" "-E" "copy"
      "${CMAKE_CURRENT_SOURCE_DIR}/${z3py_file}"
      "${z3py_bindings_build_dest}"
    DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/${z3py_file}"
    COMMENT "Copying \"${z3py_file}\" to ${z3py_bindings_build_dest}"
  )
  list(APPEND build_z3_python_bindings_target_depends "${z3py_bindings_build_dest}/${z3py_file}")
endforeach()

# Generate z3core.py
add_custom_command(OUTPUT "${z3py_bindings_build_dest}/z3core.py"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${CMAKE_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--z3py-output-dir"
    "${z3py_bindings_build_dest}"
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${CMAKE_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
    # FIXME: When update_api.py no longer uses ``mk_util`` drop this dependency
    "${CMAKE_SOURCE_DIR}/scripts/mk_util.py"
  COMMENT "Generating z3core.py"
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)
list(APPEND build_z3_python_bindings_target_depends "${z3py_bindings_build_dest}/z3core.py")

# Generate z3consts.py
add_custom_command(OUTPUT "${z3py_bindings_build_dest}/z3consts.py"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${CMAKE_SOURCE_DIR}/scripts/mk_consts_files.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--z3py-output-dir"
    "${z3py_bindings_build_dest}"
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${CMAKE_SOURCE_DIR}/scripts/mk_consts_files.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
  COMMENT "Generating z3consts.py"
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)
list(APPEND build_z3_python_bindings_target_depends "${z3py_bindings_build_dest}/z3consts.py")

# Convenient top-level target
add_custom_target(build_z3_python_bindings
  ALL
  DEPENDS
    ${build_z3_python_bindings_target_depends}
)

###############################################################################
# Install
###############################################################################
option(INSTALL_PYTHON_BINDINGS "Install Python bindings when invoking install target" ON)
if (INSTALL_PYTHON_BINDINGS)
  # Determine the installation path for the bindings
  message(STATUS "Emitting rules to install Z3 python bindings")
  execute_process(
    COMMAND "${PYTHON_EXECUTABLE}" "-c"
      "import distutils.sysconfig; print(distutils.sysconfig.get_python_lib())"
    RESULT_VARIABLE exit_code
    OUTPUT_VARIABLE python_pkg_dir
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )

  if (NOT ("${exit_code}" EQUAL 0))
    message(FATAL_ERROR "Failed to determine your Python package directory")
  endif()
  message(STATUS "Detected Python package directory: \"${python_pkg_dir}\"")

  # Check if path exists under the install prefix
  set(python_install_dir "")
  string(FIND "${python_pkg_dir}" "${CMAKE_INSTALL_PREFIX}" position)
  if (NOT ("${position}" EQUAL 0))
    message(WARNING "The detected Python package directory \"${python_pkg_dir}\" "
            "does not exist under the install prefix \"${CMAKE_INSTALL_PREFIX}\"."
            " Running the install target may lead to a broken installation."
           )
  endif()
  # Using DESTDIR still seems to work even if we use an absolute path
  set(python_install_dir "${python_pkg_dir}")
  message(STATUS "Python bindings will be installed to \"${python_install_dir}\"")
  install(FILES ${build_z3_python_bindings_target_depends}
    DESTINATION "${python_install_dir}"
  )
else()
  message(STATUS "Not emitting rules to install Z3 python bindings")
endif()
