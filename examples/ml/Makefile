# This is a temporary support file for emacs annotations. 
# It does not compile the Z3 ML example; this will be built 
# in the top-level build directory.

all: 
	source /cygdrive/c/cwinter/.msenv32 ; OCAML_COMPAT=c C:/ocamlw32/bin/ocamlc -g -custom -cclib '-L../../bld_dbg -lz3' -annot -o ml_example.byte -I ../../bld_dbg/api/ml z3.cma ml_example.ml
	source /cygdrive/c/cwinter/.msenv32 ; C:/ocamlw32/bin/ocamlopt -g -annot -o ml_example -cclib '-L../../bld_dbg -lz3' -I ../../bld_dbg -I ../../bld_dbg/api/ml z3.cmxa ml_example.ml
