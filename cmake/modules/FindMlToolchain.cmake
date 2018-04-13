# Tries to find a working OCaml tool chain

include(FindPackageHandleStandardArgs)

find_program(
  OCAMLC_EXECUTABLE
  NAMES "ocamlc"
)
message(STATUS "OCAMLC_EXECUTABLE: \"${OCAMLC_EXECUTABLE}\"")

find_program(
  OCAMLOPT_EXECUTABLE
  NAMES "ocamlopt"
)
message(STATUS "OCAMLOPT_EXECUTABLE: \"${OCAMLOPT_EXECUTABLE}\"")

find_program(
  OCAMLFIND_EXECUTABLE
  NAMES "ocamlfind"
)
message(STATUS "OCAMLFIND_EXECUTABLE: \"${OCAMLFIND_EXECUTABLE}\"")
