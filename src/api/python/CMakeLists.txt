message(STATUS "Emitting rules to build Z3 python bindings")
###############################################################################
# Add target to build python bindings for the build directory
###############################################################################
# This allows the python bindings to be used directly from the build directory
set(z3py_files
  z3/__init__.py
  z3/z3.py
  z3/z3num.py
  z3/z3poly.py
  z3/z3printer.py
  z3/z3rcf.py
  z3test.py
  z3/z3types.py
  z3/z3util.py
)

set(z3py_bindings_build_dest "${PROJECT_BINARY_DIR}/python")
file(MAKE_DIRECTORY "${z3py_bindings_build_dest}")
file(MAKE_DIRECTORY "${z3py_bindings_build_dest}/z3")

set(build_z3_python_bindings_target_depends "")
foreach (z3py_file ${z3py_files})
  add_custom_command(OUTPUT "${z3py_bindings_build_dest}/${z3py_file}"
    COMMAND "${CMAKE_COMMAND}" "-E" "copy"
      "${CMAKE_CURRENT_SOURCE_DIR}/${z3py_file}"
      "${z3py_bindings_build_dest}/${z3py_file}"
    DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/${z3py_file}"
    COMMENT "Copying \"${z3py_file}\" to ${z3py_bindings_build_dest}/${z3py_file}"
  )
  list(APPEND build_z3_python_bindings_target_depends "${z3py_bindings_build_dest}/${z3py_file}")
endforeach()

# Generate z3core.py
add_custom_command(OUTPUT "${z3py_bindings_build_dest}/z3/z3core.py"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${PROJECT_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--z3py-output-dir"
    "${z3py_bindings_build_dest}"
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${PROJECT_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
    # FIXME: When update_api.py no longer uses ``mk_util`` drop this dependency
    "${PROJECT_SOURCE_DIR}/scripts/mk_util.py"
  COMMENT "Generating z3core.py"
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)
list(APPEND build_z3_python_bindings_target_depends "${z3py_bindings_build_dest}/z3/z3core.py")

# Generate z3consts.py
add_custom_command(OUTPUT "${z3py_bindings_build_dest}/z3/z3consts.py"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${PROJECT_SOURCE_DIR}/scripts/mk_consts_files.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--z3py-output-dir"
    "${z3py_bindings_build_dest}"
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${PROJECT_SOURCE_DIR}/scripts/mk_consts_files.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
  COMMENT "Generating z3consts.py"
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)
list(APPEND build_z3_python_bindings_target_depends "${z3py_bindings_build_dest}/z3/z3consts.py")

if (UNIX)
  set(LINK_COMMAND "create_symlink")
else()
  set(LINK_COMMAND "copy")
endif()

# Link libz3 into the python directory so bindings work out of the box
add_custom_command(OUTPUT "${z3py_bindings_build_dest}/libz3${CMAKE_SHARED_MODULE_SUFFIX}"
  COMMAND "${CMAKE_COMMAND}" "-E" "${LINK_COMMAND}"
    "${PROJECT_BINARY_DIR}/libz3${CMAKE_SHARED_MODULE_SUFFIX}"
    "${z3py_bindings_build_dest}/libz3${CMAKE_SHARED_MODULE_SUFFIX}"
  DEPENDS libz3
  COMMENT "Linking libz3 into python directory"
)

# Convenient top-level target
add_custom_target(build_z3_python_bindings
  ALL
  DEPENDS
    ${build_z3_python_bindings_target_depends}
    "${z3py_bindings_build_dest}/libz3${CMAKE_SHARED_MODULE_SUFFIX}"
)

###############################################################################
# Install
###############################################################################
option(Z3_INSTALL_PYTHON_BINDINGS "Install Python bindings when invoking install target" ON)
if (Z3_INSTALL_PYTHON_BINDINGS)
  message(STATUS "Emitting rules to install Z3 python bindings")
  # Try to guess the installation path for the bindings
  if (NOT DEFINED CMAKE_INSTALL_PYTHON_PKG_DIR)
    message(STATUS "CMAKE_INSTALL_PYTHON_PKG_DIR not set. Trying to guess")
    execute_process(
      COMMAND "${PYTHON_EXECUTABLE}" "-c"
        "import distutils.sysconfig; print(distutils.sysconfig.get_python_lib())"
      RESULT_VARIABLE exit_code
      OUTPUT_VARIABLE CMAKE_INSTALL_PYTHON_PKG_DIR
      OUTPUT_STRIP_TRAILING_WHITESPACE
    )

    if (NOT ("${exit_code}" EQUAL 0))
      message(FATAL_ERROR "Failed to determine your Python package directory")
    endif()
    message(STATUS "Detected Python package directory: \"${CMAKE_INSTALL_PYTHON_PKG_DIR}\"")
    # Set a cache variable that the user can modify if needed
    set(CMAKE_INSTALL_PYTHON_PKG_DIR
      "${CMAKE_INSTALL_PYTHON_PKG_DIR}"
      CACHE PATH
      "Path to install python bindings. This can be relative or absolute.")
    mark_as_advanced(CMAKE_INSTALL_PYTHON_PKG_DIR)
  else()
    message(STATUS "CMAKE_INSTALL_PYTHON_PKG_DIR already set (\"${CMAKE_INSTALL_PYTHON_PKG_DIR}\")"
                   ". Not trying to guess.")
  endif()

  # Check if path exists under the install prefix if it is absolute. If the
  # path is relative it will be installed under the install prefix so there
  # if nothing to check
  if (IS_ABSOLUTE "${CMAKE_INSTALL_PYTHON_PKG_DIR}")
    string(FIND "${CMAKE_INSTALL_PYTHON_PKG_DIR}" "${CMAKE_INSTALL_PREFIX}" position)
    if (NOT ("${position}" EQUAL 0))
      message(WARNING "The directory to install the python bindings \"${CMAKE_INSTALL_PYTHON_PKG_DIR}\" "
              "is not under the install prefix \"${CMAKE_INSTALL_PREFIX}\"."
              " Running the install target may lead to a broken installation. "
              "To change the install directory modify the CMAKE_INSTALL_PYTHON_PKG_DIR cache variable."
              )
    endif()
  endif()
  # Using DESTDIR still seems to work even if we use an absolute path
  message(STATUS "Python bindings will be installed to \"${CMAKE_INSTALL_PYTHON_PKG_DIR}\"")
  install(FILES ${build_z3_python_bindings_target_depends}
    DESTINATION "${CMAKE_INSTALL_PYTHON_PKG_DIR}/z3"
  )
else()
  message(STATUS "Not emitting rules to install Z3 python bindings")
endif()
