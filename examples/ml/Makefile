# This is a temporary support file for emacs annotations. 
# It does not compile the Z3 ML example; this will be built 
# in the top-level build directory.

all: 
	OCAML_COMPAT=c ocamlc -g -annot -o ml_example.byte -I ../../bld_dbg -I ../../bld_dbg/api/ml z3.cma ml_example.ml
	ocamlopt -g -annot -o ml_example -I ../../bld_dbg -I ../../bld_dbg/api/ml z3.cmxa ml_example.ml
