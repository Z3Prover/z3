
# FIXME: what's the extension on windows? This is used in AddOCaml.cmake
set(CMAKE_C_OUTPUT_EXTENSION ".o")

include(FindOCaml)
include(AddOCaml)
find_package(OCaml REQUIRED)

if( NOT "${HAVE_OCAMLOPT}" )
  message(FATAL_ERROR ${error})
endif()

message("OCaml stdlib dir is ${OCAML_STDLIB_PATH}")

# Generate z3enum.ml
set(Z3_ML_ENUMS_FILE "${CMAKE_CURRENT_BINARY_DIR}/z3enums.ml")
add_custom_command(OUTPUT "${Z3_ML_ENUMS_FILE}"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${CMAKE_SOURCE_DIR}/scripts/mk_consts_files.py"
    "--ml-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${CMAKE_SOURCE_DIR}/scripts/mk_consts_files.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
    # FIXME: When mk_consts_files.py no longer uses ``mk_util`` drop this dependency
    "${CMAKE_SOURCE_DIR}/scripts/mk_util.py"
  COMMENT "Generating ${Z3_ML_ENUMS_FILE}"
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)

# Generate z3native
set(Z3_ML_NATIVE_FILE "${CMAKE_CURRENT_BINARY_DIR}/z3native.ml")
set(Z3_ML_STUBS_FILE "${CMAKE_CURRENT_BINARY_DIR}/z3native_stubs.c")
add_custom_command(OUTPUT "${Z3_ML_NATIVE_FILE}" "${Z3_ML_STUBS_FILE}"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${CMAKE_SOURCE_DIR}/scripts/update_api.py"
    "--ml-src-dir"
    "${CMAKE_CURRENT_SOURCE_DIR}/"
    "--ml-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${CMAKE_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
    "${CMAKE_SOURCE_DIR}/src/api/ml/z3native.ml.pre"
    "${CMAKE_SOURCE_DIR}/src/api/ml/z3native_stubs.c.pre"
    # FIXME: When update_api.py no longer uses ``mk_util`` drop this dependency
    "${CMAKE_SOURCE_DIR}/scripts/mk_util.py"
  COMMENT "Generating ${Z3_ML_NATIVE_FILE} ${Z3_ML_STUBS_FILE}"
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)

add_ocaml_library(z3
  OCAML z3
  OCAMLGEN z3enums z3native
  CGEN z3native_stubs
  CFLAGS "-I ../ -I ${OCAML_STDLIB_PATH}"
  PKG num)

