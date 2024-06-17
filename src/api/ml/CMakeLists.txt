# find_program(OCAMLFIND
#              NAMES ocamlfind)
# find_library(ocaml)

find_package(OCaml REQUIRED)
include(FindOCaml)
include(AddOCaml)

# A file is either copy-ed or gen-ed
# Why do I need to copy

# Generate ``z3native.ml`` and ``z3native_stubs.c``
# ${PROJECT_SOURCE_DIR}:       /vendor/z3
# ${PROJECT_BINARY_DIR}:       /vendor/z3/build
# ${CMAKE_CURRENT_SOURCE_DIR}: /vendor/z3/src/api/ml
# ${CMAKE_CURRENT_BINARY_DIR}: /vendor/z3/build/src/api/ml

set(exe_ext ${CMAKE_EXECUTABLE_SUFFIX})
set(bc_ext ".byte")

set(z3ml_src ${CMAKE_CURRENT_SOURCE_DIR})
set(z3ml_bin ${CMAKE_CURRENT_BINARY_DIR})

set(z3_api_src "${PROJECT_SOURCE_DIR}/src/api")

set(Z3ml_native_stubs_c "${z3ml_bin}/z3native_stubs.c")
add_custom_command(
  OUTPUT
    "${z3ml_bin}/z3native.ml"
    "${Z3ml_native_stubs_c}"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${PROJECT_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--ml-src-dir"
    "${CMAKE_CURRENT_SOURCE_DIR}"
    "--ml-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${PROJECT_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
  COMMENT "Generatinging ${z3ml_bin}/z3native.ml and ${Z3ml_native_stubs_c}"
  VERBATIM
)

set(z3ml_enums_ml "${z3ml_bin}/z3enums.ml")
add_custom_command(OUTPUT "${z3ml_enums_ml}"
  COMMAND "${PYTHON_EXECUTABLE}"
    "${PROJECT_SOURCE_DIR}/scripts/mk_consts_files.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--ml-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
  DEPENDS
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "${PROJECT_SOURCE_DIR}/scripts/mk_consts_files.py"
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
  COMMENT "Generating ${z3ml_enums_ml}"
  VERBATIM
)

# set(z3ml_generated_files
#   "${z3ml_bin}/z3native.ml"
#   "${Z3ml_native_stubs_c}"
#   "${z3ml_enums_ml}"
# )

# add_custom_target(ocaml_generated DEPENDS
#   ${z3ml_generated_files}
# )

# add_dependencies(z3ml ocaml_generated)

add_custom_command(
  OUTPUT  "${z3ml_bin}/z3.ml"
          "${z3ml_bin}/z3.mli"
  COMMAND "${CMAKE_COMMAND}" "-E" "copy" "${z3ml_src}/z3.ml" "${z3ml_bin}/z3.ml"
  COMMAND "${CMAKE_COMMAND}" "-E" "copy" "${z3ml_src}/z3.mli" "${z3ml_bin}/z3.mli"
  DEPENDS "${z3ml_src}/z3.mli"
  COMMENT "Copying z3.mli to build area")

add_custom_command(
  OUTPUT "${z3ml_bin}/z3enums.mli"
  COMMAND "${OCAMLFIND}" "ocamlc" 
          "-package" "zarith"
          "-i" 
          "-I" "${z3ml_bin}"
          "-c" "${z3ml_bin}/z3enums.ml"
          ">" "${z3ml_bin}/z3enums.mli"
  DEPENDS "${z3ml_enums_ml}"
  COMMENT "Building z3enums.mli"
  VERBATIM)

add_custom_command(
  OUTPUT "${z3ml_bin}/z3enums.cmo"
  COMMAND "${OCAMLFIND}" "ocamlc" 
          "-package" "zarith"
          "-I" "${z3ml_bin}"
          "-c" "${z3ml_bin}/z3enums.ml"
  DEPENDS "${z3ml_enums_ml}"
  COMMENT "Building z3enums.cmo"
  VERBATIM)

if( HAVE_OCAMLOPT )
  add_custom_command(
    OUTPUT "${z3ml_bin}/z3enums.cmx"
    COMMAND "${OCAMLFIND}" "ocamlopt" 
            "-package" "zarith"
            "-I" "${z3ml_bin}"
            "-c" "${z3ml_bin}/z3enums.ml"
    DEPENDS "${z3ml_enums_ml}"
    COMMENT "Building z3enums.cmx"
    VERBATIM)
endif()

add_custom_command(
  OUTPUT "${z3ml_bin}/z3native_stubs.o"
  COMMAND "${OCAMLFIND}" "ocamlc"
          "-package" "zarith"
          "-o" "${z3ml_bin}/z3native_stubs.o"
          "-I" "${z3ml_bin}"
          "-I" "${z3ml_src}"
          "-I" "${z3_api_src}"
          "-I" "$$(ocamlfind ocamlc -where)"
          "-c" "${Z3ml_native_stubs_c}"
  DEPENDS "${z3ml_bin}/z3enums.cmo"
          "${Z3ml_native_stubs_c}"
  COMMENT "Building z3native_stubs.o"
  USES_TERMINAL
  )

add_custom_command(
  OUTPUT "${z3ml_bin}/z3native.mli"
  COMMAND "${OCAMLFIND}" "ocamlc" 
          "-package" "zarith"
          "-i" 
          "-I" "${z3ml_bin}"
          "-c" "${z3ml_bin}/z3native.ml"
          ">" "${z3ml_bin}/z3native.mli"
  DEPENDS "${z3ml_enums_ml}"
          "${z3ml_bin}/z3enums.cmo"
          "${z3ml_bin}/z3native.ml"
  COMMENT "Building z3native.mli"
  VERBATIM)

add_custom_command(
  OUTPUT "${z3ml_bin}/z3native.cmi"
         "${z3ml_bin}/z3native.cmo"
  COMMAND "${OCAMLFIND}" "ocamlc" 
         "-package" "zarith"
         "-I" "${z3ml_bin}"
         "-c" "${z3ml_bin}/z3native.mli"  
  COMMAND "${OCAMLFIND}" "ocamlc" 
          "-package" "zarith"
          "-I" "${z3ml_bin}"
          "-c" "${z3ml_bin}/z3native.ml"
  DEPENDS "${z3ml_bin}/z3enums.cmo"
          "${z3ml_bin}/z3native.mli"
          "${z3ml_bin}/z3native.ml"
  COMMENT "Building z3native.cmo"
  VERBATIM)

if( HAVE_OCAMLOPT )
  add_custom_command(
    OUTPUT "${z3ml_bin}/z3native.cmx"
    COMMAND "${OCAMLFIND}" "ocamlopt" 
            "-package" "zarith"
            "-I" "${z3ml_bin}"
            "-c" "${z3ml_bin}/z3native.ml"
    DEPENDS "${z3ml_bin}/z3enums.cmo"
            "${z3ml_bin}/z3native.mli"
            "${z3ml_bin}/z3native.cmi"
            "${z3ml_bin}/z3native.ml"
    COMMENT "Building z3native.cmx"
    VERBATIM)
endif()

add_custom_command(
  OUTPUT "${z3ml_bin}/z3.cmi"
         "${z3ml_bin}/z3.cmo"
  COMMAND "${OCAMLFIND}" "ocamlc"
          "-package" "zarith"
          "-I" "${z3ml_bin}"
          "-c" "${z3ml_bin}/z3.mli"
  COMMAND "${OCAMLFIND}" "ocamlc"
          "-package" "zarith"
          "-I" "${z3ml_bin}"
          "-c" "${z3ml_bin}/z3.ml"
  DEPENDS "${z3ml_bin}/z3enums.cmo"
          "${z3ml_bin}/z3native.cmo"
          "${z3ml_bin}/z3.ml"
          "${z3ml_bin}/z3.mli"
  COMMENT "Building z3.cmo"
  VERBATIM)

if( HAVE_OCAMLOPT )
  add_custom_command(
    OUTPUT "${z3ml_bin}/z3.cmx"
    COMMAND "${OCAMLFIND}" "ocamlopt" 
            "-package" "zarith"
            "-I" "${z3ml_bin}"
            "-c" "${z3ml_bin}/z3.ml"  
    DEPENDS "${z3ml_bin}/z3enums.cmo"
            "${z3ml_bin}/z3native.cmo"
            "${z3ml_bin}/z3.ml"
            "${z3ml_bin}/z3.mli"
            "${z3ml_bin}/z3.cmi"
    COMMENT "Building z3.cmx"
    VERBATIM)
endif()

set(ocamlmklib_flags "-lz3" "-lstdc++" "-ldopt" "-L${PROJECT_BINARY_DIR}"
                     "-ccopt" "-L\\$CAMLORIGIN/../.."
                     "-ccopt" "-Wl,-rpath,\\$CAMLORIGIN/../.."
                     "-package" "zarith")

add_custom_command(
  OUTPUT "${z3ml_bin}/z3ml.cma"
         "${z3ml_bin}/dllz3ml.so"
         "${z3ml_bin}/libz3ml.a"
  COMMAND "${OCAMLFIND}" "ocamlmklib" "-ocamlcflags" "-bin-annot" "-L."
    "-o" z3ml
    ${ocamlmklib_flags}
    "-I" "${z3ml_bin}"
    "${z3ml_bin}/z3enums.cmo"
    "${z3ml_bin}/z3native.cmo"
    "${z3ml_bin}/z3native_stubs.o"
    "${z3ml_bin}/z3.cmo"
  DEPENDS
    libz3
    "${z3ml_bin}/z3enums.cmo"
    "${z3ml_bin}/z3native.cmo"
    "${z3ml_bin}/z3native_stubs.o"
    "${z3ml_bin}/z3.cmo"
  COMMENT "Building OCaml library ${name}"
  VERBATIM)

if( HAVE_OCAMLOPT )
  add_custom_command(
    OUTPUT "${z3ml_bin}/z3ml.cmxa"
    COMMAND "${OCAMLFIND}" "ocamlmklib" "-ocamlcflags" "-bin-annot" "-L."
      "-o" z3ml
      ${ocamlmklib_flags}
      "-I" "${z3ml_bin}"
      "${z3ml_bin}/z3enums.cmx"
      "${z3ml_bin}/z3native.cmx"
      "${z3ml_bin}/z3native_stubs.o"
      "${z3ml_bin}/z3.cmx"
    DEPENDS
      libz3
      "${z3ml_bin}/z3enums.cmx"
      "${z3ml_bin}/z3native.cmx"
      "${z3ml_bin}/z3native_stubs.o"
      "${z3ml_bin}/z3.cmx"
    COMMENT "Building OCaml library ${name}"
    VERBATIM)

  add_custom_command(
    OUTPUT "${z3ml_bin}/z3ml.cmxs"
    COMMAND "${OCAMLFIND}" "ocamlopt" "-linkall" "-shared"
      "-o" "${z3ml_bin}/z3ml.cmxs"
      "-I" "."
      "-I" "${z3ml_bin}"
      "${z3ml_bin}/z3ml.cmxa"
    DEPENDS
      "${z3ml_bin}/z3ml.cmxa"
    COMMENT "Building OCaml library ${name}"
    VERBATIM)
endif()

# -cclib "-L. -lpthread -lstdc++ -lz3"

# set (cc_flags "\"-L. -lpthread -lstdc++ -lz3\"")
#"LD_LIBRARY_PATH=${PROJECT_BINARY_DIR}"

# Example
add_custom_command(
  OUTPUT  "${z3ml_bin}/ml_example.ml"
  COMMAND "${CMAKE_COMMAND}" "-E" 
          "copy" "${PROJECT_SOURCE_DIR}/examples/ml/ml_example.ml" "${z3ml_bin}/ml_example.ml"
  DEPENDS "${PROJECT_SOURCE_DIR}/examples/ml/ml_example.ml"
  COMMENT "Copying ml_example.ml to build area")

add_custom_command(
  OUTPUT "${z3ml_bin}/ml_example${bc_ext}"
          "${z3ml_bin}/ml_example.bc.log"
  COMMAND "${OCAMLFIND}" "ocamlc" "-custom"
    "-o" "${z3ml_bin}/ml_example${bc_ext}"
    "-I" "${z3ml_bin}"
    "-cclib" "-L${PROJECT_BINARY_DIR}"
    "-cclib" [[-L. -lpthread -lstdc++ -lz3]]
    "-package" "zarith"
    "-linkpkg"
    "z3ml.cma"
    "\$(ocamlfind query zarith)/zarith.cma"
    "${z3ml_bin}/ml_example.ml"
  COMMAND 
    "ocamlrun"
    "${z3ml_bin}/ml_example${bc_ext}"
    ">" "${z3ml_bin}/ml_example.bc.log"
  DEPENDS
    "${z3ml_bin}/z3ml.cma"
    "${z3ml_bin}/ml_example.ml"
  COMMENT "Testing build and run ml_example bytecode"
  VERBATIM)

add_custom_command(
  OUTPUT "${z3ml_bin}/ml_example${exe_ext}"
         "${z3ml_bin}/ml_example.log"
  COMMAND "${OCAMLFIND}" "ocamlopt"
    "-o" "${z3ml_bin}/ml_example${exe_ext}"
    "-I" "${z3ml_bin}"
    "-cclib" "-L${PROJECT_BINARY_DIR}"
    "-cclib" [[-L. -lpthread -lstdc++ -lz3]]
    "-package" "zarith"
    "-linkpkg"
    "z3ml.cmxa"
    "${z3ml_bin}/ml_example.ml"
  COMMAND "LD_LIBRARY_PATH=${PROJECT_BINARY_DIR}" 
    "${z3ml_bin}/ml_example${exe_ext}"
    ">" "${z3ml_bin}/ml_example.log"
  DEPENDS
    "${z3ml_bin}/z3ml.cmxa"
    "${z3ml_bin}/ml_example.ml"
  COMMENT "Testing build and run ml_example natively"
  VERBATIM)

# LD_LIBRARY_PATH=build ./build/src/api/ml/ml_example
add_custom_target(build_ocaml_example
  ALL
  DEPENDS
    "${z3ml_bin}/ml_example${bc_ext}"
    "${z3ml_bin}/ml_example${exe_ext}"
)

add_custom_target(build_z3_ocaml_bindings
  ALL
  DEPENDS
    "${z3ml_bin}/z3ml.cma"
    "${z3ml_bin}/z3ml.cmxa"
    "${z3ml_bin}/z3ml.cmxs"
    "${z3ml_bin}/dllz3ml.so"
    "${z3ml_bin}/libz3ml.a"
    build_ocaml_example
)

# Link libz3 into the python directory so bindings work out of the box
# add_custom_command(OUTPUT "${z3py_bindings_build_dest}/libz3${CMAKE_SHARED_MODULE_SUFFIX}"
#   COMMAND "${CMAKE_COMMAND}" "-E" "${LINK_COMMAND}"
#     "${PROJECT_BINARY_DIR}/libz3${CMAKE_SHARED_MODULE_SUFFIX}"
#     "${z3py_bindings_build_dest}/libz3${CMAKE_SHARED_MODULE_SUFFIX}"
#   DEPENDS libz3
#   COMMENT "Linking libz3 into python directory"
# )

# add_ocaml_library(z3ml
#   OCAML    z3enums z3native z3
#   # OCAMLDEP llvm
#   PKG      zarith
#   C        z3native_stubs
#   CFLAGS   "-I${Z3_C_API_PATH} -I${CMAKE_CURRENT_SOURCE_DIR} -I\$\(ocamlfind ocamlc -where\)"
#   GEN      "${OCAML_GENERATED_FILES}"
#   # -I${CMAKE_CURRENT_SOURCE_DIR}/../llvm
#   # LLVM     IRReader)
# )


# set(z3_c_api_path "${PROJECT_SOURCE_DIR}/src/api")
# target_sources(z3ml PRIVATE
#                 z3native_stubs.h
#                 ${z3_c_api_path})


# message(heads "--${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}")
# message(extra deps "--${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}")

# add_custom_target(z3natives_stubs.c DEPENDS "${Z3_OCAML_NATIVE_STUB_PRE_FILE}")
# target_sources(ocaml_z3 
#               PRIVATE ${Z3_OCAML_NATIVE_FILE} ${Z3_OCAML_NATIVE_STUB_FILE})

# target_include_directories(ocaml_z3
#     PUBLIC ${CMAKE_CURRENT_BINARY_DIR}
# )

# add_custom_target (LibCoreBC DEPENDS libcore.bc)

# target_sources(src/api/ml/z3natives_stubs.c
#                 PUBLIC Z3_OCAML_NATIVE_STUB_FILE)

# add_custom_target(${Z3_OCAML_NATIVE_STUB_FILE} DEPENDS 
#                  ${Z3_OCAML_NATIVE_STUB_PRE_FILE})

# target_precompile_headers(
#   ocaml_z3 PRIVATE
#   z3native_stubs.h
# )

# target_sources(ocaml_z3 PRIVATE
#                 "${PROJECT_SOURCE_DIR}/src/api/ml/z3native.ml"
#                 "${PROJECT_SOURCE_DIR}/src/api/ml/z3native_stubs.c")

# add_dependencies(ocaml_z3
#               "${PROJECT_SOURCE_DIR}/src/api"
#               "${PROJECT_BINARY_DIR}/src/api"
#             )

# find_package(OCaml)
# message("DDDebug ${OCAMLFIND}")
# message("DDDebug ${pkg}")
# find_ocamlfind_package(ctypes)
# # find_ocamlfind_package("nonexist")
# message(small " ${HAVE_OCAML_ctype}")
# message(caps " ${HAVE_OCAML_CTYPES}")
# message(small " ${OCAML_ctype_VERSION}")
# message(caps " ${OCAML_CTYPES_VERSION}")
# find_package(ocaml REQUIRED)

# add_custom_target(ocaml_post_z3enums DEPENDS
#   "${CMAKE_CURRENT_BINARY_DIR}/z3enums.ml"
#   "${CMAKE_CURRENT_BINARY_DIR}/z3enums.mli"
#   "${CMAKE_CURRENT_BINARY_DIR}/z3enums.cmo"
#   "${CMAKE_CURRENT_BINARY_DIR}/z3enums.cmx"
# )
# add_custom_target(z3.ml DEPENDS
#   ocaml_post_z3enums
# )
# add_custom_target(z3native.ml DEPENDS
#   ocaml_post_z3enums
# )
