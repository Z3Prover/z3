find_package(OCaml REQUIRED)
# ${PROJECT_SOURCE_DIR}:       /vendor/z3
# ${PROJECT_BINARY_DIR}:       /vendor/z3/build
# ${CMAKE_CURRENT_SOURCE_DIR}: /vendor/z3/src/api/ml
# ${CMAKE_CURRENT_BINARY_DIR}: /vendor/z3/build/src/api/ml

set(exe_ext ${CMAKE_EXECUTABLE_SUFFIX})
set(bc_ext ".byte")

set(z3ml_src ${CMAKE_CURRENT_SOURCE_DIR})
set(z3ml_bin ${CMAKE_CURRENT_BINARY_DIR})

if (Z3_BUILD_OCAML_EXTERNAL_LIBZ3)
  add_custom_target(libz3_z3ml
    ALL
    DEPENDS "${Z3_BUILD_OCAML_EXTERNAL_LIBZ3}/libz3.so"
  )
  set(libz3_path ${Z3_BUILD_OCAML_EXTERNAL_LIBZ3})
else()
  add_custom_target(libz3_z3ml
    ALL
    DEPENDS libz3
  )
  set(libz3_path ${PROJECT_BINARY_DIR})
endif()

message(libz3_path "${libz3_path}")

add_custom_command(
  OUTPUT
    "${z3ml_bin}/z3native.ml"
    "${z3ml_bin}/z3native_stubs.c"
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
  COMMENT "Generatinging ${z3ml_bin}/z3native.ml and ${z3ml_bin}/z3native_stubs.c"
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

add_custom_command(
  OUTPUT  "${z3ml_bin}/z3.ml"
          "${z3ml_bin}/z3.mli"
  COMMAND "${CMAKE_COMMAND}" "-E" "copy" "${z3ml_src}/z3.ml" "${z3ml_bin}/z3.ml"
  COMMAND "${CMAKE_COMMAND}" "-E" "copy" "${z3ml_src}/z3.mli" "${z3ml_bin}/z3.mli"
  DEPENDS "${z3ml_src}/z3.ml"
          "${z3ml_src}/z3.mli"
  COMMENT "Copying z3.ml and z3.mli to build area")

set(z3ml_common_flags  "-package" "zarith"
                       "-I" "${z3ml_bin}")

# z3native_stubs.c depends on nothing

add_custom_command(
  OUTPUT "${z3ml_bin}/z3native_stubs.o"
  COMMAND "${OCAMLFIND}" "ocamlc" ${z3ml_common_flags}
          "-o" "${z3ml_bin}/z3native_stubs.o"
          "-I" "${z3ml_src}"
          "-I" "${PROJECT_SOURCE_DIR}/src/api"
          "-I" "$$(ocamlfind ocamlc -where)"
          "-c" "${z3ml_bin}/z3native_stubs.c"
  DEPENDS "${z3ml_bin}/z3native_stubs.c"
  COMMENT "Building z3native_stubs.o"
  USES_TERMINAL)

# z3enum.ml depends on nothing

add_custom_command(
  OUTPUT "${z3ml_bin}/z3enums.mli"
         "${z3ml_bin}/z3enums.cmi"
         "${z3ml_bin}/z3enums.cmo"
         "${z3ml_bin}/z3enums.cmx"
  COMMAND "${OCAMLFIND}" "ocamlc"   ${z3ml_common_flags}
         "-i" 
         "-c" "${z3ml_bin}/z3enums.ml"
         ">" "${z3ml_bin}/z3enums.mli"
  COMMAND "${OCAMLFIND}" "ocamlc"   ${z3ml_common_flags}
         "-c" "${z3ml_bin}/z3enums.mli"  
  COMMAND "${OCAMLFIND}" "ocamlc"   ${z3ml_common_flags}
         "-c" "${z3ml_bin}/z3enums.ml"
  COMMAND "${OCAMLFIND}" "ocamlopt" ${z3ml_common_flags}
          "-c" "${z3ml_bin}/z3enums.ml"
  DEPENDS "${z3ml_enums_ml}"
  COMMENT "Building z3enums.{mli,cmi,cmo,cmx}"
  VERBATIM)

# z3native.ml depends on z3enums

add_custom_command(
  OUTPUT "${z3ml_bin}/z3native.mli"
         "${z3ml_bin}/z3native.cmi"
         "${z3ml_bin}/z3native.cmo"
         "${z3ml_bin}/z3native.cmx"
  COMMAND "${OCAMLFIND}" "ocamlc"   ${z3ml_common_flags}
         "-i" 
         "-c" "${z3ml_bin}/z3native.ml"
         ">" "${z3ml_bin}/z3native.mli"
  COMMAND "${OCAMLFIND}" "ocamlc"   ${z3ml_common_flags}
         "-c" "${z3ml_bin}/z3native.mli"  
  COMMAND "${OCAMLFIND}" "ocamlc"   ${z3ml_common_flags}
          "-c" "${z3ml_bin}/z3native.ml"
  COMMAND "${OCAMLFIND}" "ocamlopt" ${z3ml_common_flags}
          "-c" "${z3ml_bin}/z3native.ml"
  DEPENDS "${z3ml_bin}/z3enums.cmo"
          "${z3ml_bin}/z3native.ml"
  COMMENT "Building z3native.{mli,cmi,cmo,cmx}"
  VERBATIM)

# z3.ml depends on z3enums and z3native

add_custom_command(
  OUTPUT "${z3ml_bin}/z3.cmi"
         "${z3ml_bin}/z3.cmo"
         "${z3ml_bin}/z3.cmx"
  COMMAND "${OCAMLFIND}" "ocamlc"   ${z3ml_common_flags}
          "-c" "${z3ml_bin}/z3.mli"
  COMMAND "${OCAMLFIND}" "ocamlc"   ${z3ml_common_flags}
          "-c" "${z3ml_bin}/z3.ml"
  COMMAND "${OCAMLFIND}" "ocamlopt" ${z3ml_common_flags}
          "-c" "${z3ml_bin}/z3.ml" 
  DEPENDS "${z3ml_bin}/z3enums.cmo"
          "${z3ml_bin}/z3native.cmo"
          "${z3ml_bin}/z3.ml"
          "${z3ml_bin}/z3.mli"
  COMMENT "Building z3.cmo"
  VERBATIM)

execute_process(
  COMMAND ${OCAMLFIND} printconf destdir
  OUTPUT_VARIABLE ocaml_destdir_path
  OUTPUT_STRIP_TRAILING_WHITESPACE)

set(ocaml_stublibs_path "${ocaml_destdir_path}/stublibs")

set(ocamlmklib_flags "-o" "z3ml"
                     "-ocamlcflags" "-bin-annot"
                     "-package" "zarith"
                     "-lz3" "-lstdc++" "-lpthread"
                     "-L${libz3_path}"
                     "-dllpath" "${libz3_path}"
                     "-L${ocaml_stublibs_path}"
                     "-dllpath" "${ocaml_stublibs_path}"
                     "-I" "${z3ml_bin}")

add_custom_command(
  OUTPUT "${z3ml_bin}/dllz3ml.so"
         "${z3ml_bin}/libz3ml.a"
         "${z3ml_bin}/z3ml.cma"
         "${z3ml_bin}/z3ml.cmxa"
         "${z3ml_bin}/z3ml.cmxs"
  COMMAND "${OCAMLFIND}" "ocamlmklib" ${ocamlmklib_flags}
    "${z3ml_bin}/z3enums.cmo"
    "${z3ml_bin}/z3native.cmo"
    "${z3ml_bin}/z3native_stubs.o"
    "${z3ml_bin}/z3.cmo"
  COMMAND "${OCAMLFIND}" "ocamlmklib" ${ocamlmklib_flags}
    "${z3ml_bin}/z3enums.cmx"
    "${z3ml_bin}/z3native.cmx"
    "${z3ml_bin}/z3native_stubs.o"
    "${z3ml_bin}/z3.cmx"  
  COMMAND "${OCAMLFIND}" "ocamlopt" "-linkall" "-shared"
    "-o" "${z3ml_bin}/z3ml.cmxs"
    "-I" "${z3ml_bin}"
    "${z3ml_bin}/z3ml.cmxa"
   DEPENDS
    libz3_z3ml
    "${z3ml_bin}/z3native_stubs.o"
    "${z3ml_bin}/z3enums.cmo"
    "${z3ml_bin}/z3native.cmo"
    "${z3ml_bin}/z3.cmo"
    "${z3ml_bin}/z3enums.cmx"
    "${z3ml_bin}/z3native.cmx"
    "${z3ml_bin}/z3.cmx"
  COMMENT "Building z3ml.{cma,cmxa,cmxs}, dllz3ml.so, and libz3ml.a"
  VERBATIM)

# Example
add_custom_command(
  OUTPUT  "${z3ml_bin}/ml_example.ml"
  COMMAND "${CMAKE_COMMAND}" "-E" 
          "copy" "${PROJECT_SOURCE_DIR}/examples/ml/ml_example.ml" "${z3ml_bin}/ml_example.ml"
  DEPENDS "${PROJECT_SOURCE_DIR}/examples/ml/ml_example.ml"
  COMMENT "Copying ml_example.ml to build area")

execute_process(
  COMMAND ${OCAMLFIND} query zarith
  OUTPUT_VARIABLE ocaml_pkg_zarith_path
  OUTPUT_STRIP_TRAILING_WHITESPACE)

add_custom_command(
  OUTPUT "${z3ml_bin}/ml_example${bc_ext}"
         "${z3ml_bin}/ml_example.bc.log"
  COMMAND "${OCAMLFIND}" "ocamlc"
    "-o" "${z3ml_bin}/ml_example${bc_ext}"
    "-package" "zarith"
    "-I" "+threads"
    "-I" "${z3ml_bin}"
    "-dllpath" "${z3ml_bin}"
    "-I" ${ocaml_stublibs_path}
    "-dllpath" ${ocaml_stublibs_path}
    "${ocaml_pkg_zarith_path}/zarith.cma"
    "${z3ml_bin}/z3ml.cma"
    "${z3ml_bin}/ml_example.ml"
  COMMAND 
    "ocamlrun" "${z3ml_bin}/ml_example${bc_ext}"
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
    "-I" "+threads"
    "-package" "zarith"
    "-linkpkg"
    "-I" "${z3ml_bin}"
    "${z3ml_bin}/z3ml.cmxa"
    "${z3ml_bin}/ml_example.ml"
  COMMAND "${z3ml_bin}/ml_example${exe_ext}"
    ">" "${z3ml_bin}/ml_example.log"
  DEPENDS
    "${z3ml_bin}/z3ml.cmxa"
    "${z3ml_bin}/ml_example.ml"
  COMMENT "Testing build and run ml_example natively"
  VERBATIM)

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
