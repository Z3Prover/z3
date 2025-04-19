find_package(OCaml REQUIRED)

set(exe_ext ${CMAKE_EXECUTABLE_SUFFIX})
set(so_ext ${CMAKE_SHARED_LIBRARY_SUFFIX})
set(bc_ext ".byte")

set(z3ml_src ${CMAKE_CURRENT_SOURCE_DIR})
set(z3ml_bin ${CMAKE_CURRENT_BINARY_DIR})

if (Z3_BUILD_OCAML_EXTERNAL_LIBZ3)
  add_custom_target(libz3_z3ml
    ALL
    DEPENDS ${Z3_BUILD_OCAML_EXTERNAL_LIBZ3}/libz3${so_ext}
  )
  set(libz3_path ${Z3_BUILD_OCAML_EXTERNAL_LIBZ3})
else()
  add_custom_target(libz3_z3ml
    ALL
    DEPENDS libz3
  )
  set(libz3_path ${PROJECT_BINARY_DIR})
endif()

add_custom_command(
  OUTPUT
    ${z3ml_bin}/z3native.ml
    ${z3ml_bin}/z3native_stubs.c
  COMMAND "${Python3_EXECUTABLE}"
    "${PROJECT_SOURCE_DIR}/scripts/update_api.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--ml-src-dir"
    "${CMAKE_CURRENT_SOURCE_DIR}"
    "--ml-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
  DEPENDS
    ${PROJECT_SOURCE_DIR}/scripts/update_api.py
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
  COMMENT "Generatinging ${z3ml_bin}/z3native.ml and ${z3ml_bin}/z3native_stubs.c"
  VERBATIM
)

add_custom_command(
  OUTPUT 
    ${z3ml_bin}/z3enums.ml
  COMMAND "${Python3_EXECUTABLE}"
    "${PROJECT_SOURCE_DIR}/scripts/mk_consts_files.py"
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    "--ml-output-dir"
    "${CMAKE_CURRENT_BINARY_DIR}"
  DEPENDS
    ${PROJECT_SOURCE_DIR}/scripts/mk_consts_files.py
    ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
  COMMENT "Generating ${z3ml_bin}/z3enums.ml"
  VERBATIM
)


set(z3ml_common_flags  "-package" "zarith"
                       "-I" "${z3ml_bin}")

                       # add_custom_command(
#   OUTPUT  ${z3ml_bin}/z3.ml
#           ${z3ml_bin}/z3.mli
#   COMMAND "${CMAKE_COMMAND}" "-E" "copy" "${z3ml_src}/z3.ml" "${z3ml_bin}/z3.ml"
#   COMMAND "${CMAKE_COMMAND}" "-E" "copy" "${z3ml_src}/z3.mli" "${z3ml_bin}/z3.mli"
#   DEPENDS ${z3ml_src}/z3.ml
#           ${z3ml_src}/z3.mli
#   COMMENT "Copying z3.ml and z3.mli to build area")

# z3native_stubs.c depends on nothing
execute_process(
  COMMAND ${OCAMLFIND} ocamlc "-where"
  OUTPUT_VARIABLE ocaml_stub_lib_path
  OUTPUT_STRIP_TRAILING_WHITESPACE)

add_custom_command(
  OUTPUT ${z3ml_bin}/z3native_stubs.o
  COMMAND "${OCAMLFIND}" "ocamlc" ${z3ml_common_flags}
          "-o" "${z3ml_bin}/z3native_stubs.o"
          "-I" "${z3ml_src}"
          "-I" "${PROJECT_SOURCE_DIR}/src/api"
          "-I" "${ocaml_stub_lib_path}"
          "-c" "${z3ml_bin}/z3native_stubs.c"
  DEPENDS ${z3ml_bin}/z3native_stubs.c
  COMMENT "Building z3native_stubs.o"
  VERBATIM)

message(STATUS "PATH: $ENV{PATH}")
message(STATUS "OCAMLFIND: $ENV{OCAMLFIND}")

# z3enum.ml depends on nothing
add_custom_command(
  OUTPUT ${z3ml_bin}/z3enums.mli
         ${z3ml_bin}/z3enums.cmi
         ${z3ml_bin}/z3enums.cmo
         ${z3ml_bin}/z3enums.cmx
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
  DEPENDS ${z3ml_bin}/z3enums.ml
  COMMENT "Building z3enums.{mli,cmi,cmo,cmx}"
  VERBATIM)

# z3native.ml depends on z3enums
add_custom_command(
  OUTPUT ${z3ml_bin}/z3native.mli
         ${z3ml_bin}/z3native.cmi
         ${z3ml_bin}/z3native.cmo
         ${z3ml_bin}/z3native.cmx
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
  DEPENDS ${z3ml_bin}/z3enums.cmo
          ${z3ml_bin}/z3native.ml
  COMMENT "Building z3native.{mli,cmi,cmo,cmx}"
  VERBATIM)

# z3.ml depends on z3enums and z3native
add_custom_command(
  OUTPUT ${z3ml_bin}/z3.cmi
         ${z3ml_bin}/z3.cmo
         ${z3ml_bin}/z3.cmx
 # COMMAND "${OCAMLFIND}" "ocamlc"   ${z3ml_common_flags}
  #         "-c" "${z3ml_bin}/z3.mli"
  # COMMAND "${OCAMLFIND}" "ocamlc"   ${z3ml_common_flags}
  #         "-c" "${z3ml_bin}/z3.ml"
  # COMMAND "${OCAMLFIND}" "ocamlopt" ${z3ml_common_flags}
  #         "-c" "${z3ml_bin}/z3.ml" 
COMMAND "${OCAMLFIND}" "ocamlc"   ${z3ml_common_flags}
  "-o" "${z3ml_bin}/z3.cmi"
  "-c" "${z3ml_src}/z3.mli"
COMMAND "${OCAMLFIND}" "ocamlc"   ${z3ml_common_flags}
  "-o" "${z3ml_bin}/z3.cmo"
  "-c" "${z3ml_src}/z3.ml"
COMMAND "${OCAMLFIND}" "ocamlopt" ${z3ml_common_flags}
  "-o" "${z3ml_bin}/z3.cmx"
  "-c" "${z3ml_src}/z3.ml" 
  DEPENDS ${z3ml_bin}/z3enums.cmo
          ${z3ml_bin}/z3native.cmo
          # ${z3ml_bin}/z3.ml
          # ${z3ml_bin}/z3.mli
          ${z3ml_src}/z3.ml
          ${z3ml_src}/z3.mli
  COMMENT "Building z3.cmo"
  VERBATIM)

# making ocaml stublibs  
execute_process(
  COMMAND ${OCAMLFIND} printconf destdir
  OUTPUT_VARIABLE ocaml_destdir_path
  OUTPUT_STRIP_TRAILING_WHITESPACE)

set(ocaml_stublibs_path "${ocaml_destdir_path}/stublibs")

set(c_lib_deps "-L${libz3_path}" "-lz3" "-lstdc++" "-lpthread")
if (Z3_USE_LIB_GMP)
  list(APPEND c_lib_deps "-lgmp")
endif()

if( APPLE )
  # set(ocaml_rpath "@executable_path/../libz3${so_ext}")
elseif( UNIX )
  set(ocaml_rpath "\\$ORIGIN/../libz3${so_ext}")
  list(APPEND c_lib_deps "-dllpath" ${ocaml_rpath})
endif()

# We may not directly use CMake's BUILD_RPATH or INSTALL_RPATH since they don't set 
# the ocaml stub libraries as a normal library target.

set(ocamlmklib_flags "-o" "z3ml"
                     "-ocamlcflags" "-bin-annot"
                     "-package" "zarith"
                     ${c_lib_deps}
                     "-dllpath" "${libz3_path}"
                     "-L${ocaml_stublibs_path}"
                     "-dllpath" "${ocaml_stublibs_path}"
                     "-dllpath" "@rpath/dllz3ml.so"
                     "-I" "${z3ml_bin}")

# OCaml's dll stublib hava platform-independent name `dll<pkg>.so`

add_custom_command(
  OUTPUT ${z3ml_bin}/dllz3ml.so
         ${z3ml_bin}/libz3ml.a
         ${z3ml_bin}/z3ml.cma
         ${z3ml_bin}/z3ml.cmxa
         ${z3ml_bin}/z3ml.cmxs
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
          ${z3ml_bin}/z3native_stubs.o
          ${z3ml_bin}/z3enums.cmo
          ${z3ml_bin}/z3native.cmo
          ${z3ml_bin}/z3.cmo
          ${z3ml_bin}/z3enums.cmx
          ${z3ml_bin}/z3native.cmx
          ${z3ml_bin}/z3.cmx
  COMMENT "Building z3ml.{cma,cmxa,cmxs}, dllz3ml.so, and libz3ml.a"
  VERBATIM)

###############################################################################
# Example
###############################################################################

execute_process(
  COMMAND ${OCAMLFIND} query zarith
  OUTPUT_VARIABLE ocaml_pkg_zarith_path
  OUTPUT_STRIP_TRAILING_WHITESPACE)
  
# Always define patch_z3ml_dylib for dependency consistency
if(APPLE)
  add_custom_command(
    OUTPUT ${z3ml_bin}/patched_dllz3ml
    COMMAND install_name_tool -id "$<TARGET_FILE:libz3>" "$<TARGET_FILE:libz3>"
    COMMAND install_name_tool -change "@rpath/libz3.${Z3_VERSION_MAJOR}.${Z3_VERSION_MINOR}.dylib" "$<TARGET_FILE:libz3>" "${z3ml_bin}/dllz3ml.so"
    COMMAND touch ${z3ml_bin}/patched_dllz3ml
    DEPENDS ${z3ml_bin}/dllz3ml.so
    COMMENT "Patch install name and reference for macOS"
    VERBATIM
  )
else()
  add_custom_command(
    OUTPUT ${z3ml_bin}/patched_dllz3ml
    COMMAND ${CMAKE_COMMAND} -E touch ${z3ml_bin}/patched_dllz3ml
    COMMENT "Dummy patch target for non-macOS"
    VERBATIM
  )
endif()

add_custom_target(patch_z3ml_dylib ALL
  DEPENDS ${z3ml_bin}/patched_dllz3ml)

add_custom_target(build_z3_ocaml_bindings
  ALL
  DEPENDS
    ${z3ml_bin}/z3ml.cma
    ${z3ml_bin}/z3ml.cmxa
    ${z3ml_bin}/z3ml.cmxs
    ${z3ml_bin}/dllz3ml.so
    ${z3ml_bin}/libz3ml.a
    patch_z3ml_dylib
)

# test

set(z3ml_example_src ${PROJECT_SOURCE_DIR}/examples/ml/ml_example.ml)

add_custom_command(
  TARGET build_z3_ocaml_bindings POST_BUILD
  COMMAND "${OCAMLFIND}" ocamlc
    -o "${z3ml_bin}/ml_example.byte"
    -package zarith
    -linkpkg
    -I "${z3ml_bin}"
    -dllpath "${z3ml_bin}"
    "${z3ml_bin}/z3ml.cma"
    "${z3ml_example_src}"
  COMMAND ocamlrun "${z3ml_bin}/ml_example.byte" > "${z3ml_bin}/ml_example.bc.log"
  COMMENT "Run OCaml bytecode example"
  VERBATIM
)

add_custom_command(
  TARGET build_z3_ocaml_bindings POST_BUILD
  COMMAND "${OCAMLFIND}" ocamlopt
    -o "${z3ml_bin}/ml_example"
    -package zarith
    -linkpkg
    -I "${z3ml_bin}"
    "${z3ml_bin}/z3ml.cmxa"
    "${z3ml_example_src}"
  COMMAND "${z3ml_bin}/ml_example" > "${z3ml_bin}/ml_example.log"
  COMMENT "Run OCaml native example"
  VERBATIM
)

###############################################################################
# Install
###############################################################################

# Hacky: When the os is APPLE, a fix command will mutate `libz3.dylib` and `dlllibz3.so` inplace.
# I don't know how to use conditional `COMMAND` nor specify a file dependency for itself
# Renaming it and back seems a simple solution.

#   COMMAND mv "${z3ml_bin}/dllz3ml.so" "${z3ml_bin}/dllz3ml.pre.so"
# if (NOT APPLE)
#   add_custom_command(
#     OUTPUT "${z3ml_bin}/dllz3ml.so"
#     COMMAND mv "${z3ml_bin}/dllz3ml.pre.so" "${z3ml_bin}/dllz3ml.so}"
#     DEPENDS "${z3ml_bin}/dllz3ml.pre.so"
#   )
# else()
#   # if IS_OSX:
#   # install_name_tool -id ${stubs_install_path}/libz3.dylib libz3.dylib
#   # install_name_tool -change libz3.dylib ${stubs_install_path}/libz3.dylib api/ml/dllz3ml.so
#   add_custom_command(
#     OUTPUT "${z3ml_bin}/dllz3ml.so"
#     COMMAND mv "${z3ml_bin}/dllz3ml.pre.so" "${z3ml_bin}/dllz3ml.so"
#     DEPENDS "${z3ml_bin}/dllz3ml.so"
#   )
# endif()