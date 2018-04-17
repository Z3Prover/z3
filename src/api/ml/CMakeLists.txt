
include(FindOCaml)
include(AddOCaml)
find_package(OCaml REQUIRED)

# Generate z3enum.ml
set(Z3_ML_NATIVE_FILE "${CMAKE_CURRENT_BINARY_DIR}/z3enums.ml")
add_custom_command(OUTPUT "${Z3_ML_NATIVE_FILE}"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${CMAKE_SOURCE_DIR}/scripts/update_api.py"
    "--ml-src-dir"
    "${CMAKE_CURRENT_BINARY_DIR}/"
    "--ml-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${CMAKE_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
    # FIXME: When update_api.py no longer uses ``mk_util`` drop this dependency
    "${CMAKE_SOURCE_DIR}/scripts/mk_util.py"
  COMMENT "Generating ${Z3_ML_NATIVE_FILE}"
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)

add_ocaml_library(z3
  OCAML z3native z3
  OCAMLGEN z3enums
  C z3native_stubs
  CFLAGS -std=c++11
  PKG num)

