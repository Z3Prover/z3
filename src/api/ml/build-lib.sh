#!/bin/bash

# Script to compile the Z3 OCaml API
# Expects to find ../lib/libz3{,_dbg}.{a,so,dylib}

CFLAGS="-ccopt -Wno-discard-qual"
XCDBG="-g -ccopt -g $CFLAGS"
XCOPT="-ccopt -O3 -ccopt -fomit-frame-pointer $CFLAGS"


ocamlc -c $XCDBG z3_stubs.c z3_theory_stubs.c z3.mli z3.ml

ocamlopt -c $XCDBG z3_stubs.c z3_theory_stubs.c z3.mli z3.ml

ar rcs libz3stubs_dbg.a z3.o z3_stubs.o z3_theory_stubs.o

ocamlopt -c $XCOPT z3_stubs.c z3_theory_stubs.c z3.mli z3.ml

ar rcs libz3stubs.a z3.o z3_stubs.o z3_theory_stubs.o

ocamlc -custom -a $XCDBG -cclib -L$PWD/../lib -cclib -lz3_dbg -cclib -lcamlidl -cclib -lz3stubs_dbg z3.cmo -o z3_dbg.cma

ocamlc -custom -a $XCDBG -cclib -L$PWD/../lib -cclib -lz3 -cclib -lcamlidl -cclib -lz3stubs z3.cmo -o z3.cma

ocamlopt -a $XCDBG -cclib -L$PWD/../lib -cclib -lz3_dbg -cclib -lcamlidl -cclib -lz3stubs_dbg z3.cmx -o z3_dbg.cmxa

ocamlopt -a $XCOPT -cclib -L$PWD/../lib -cclib -lz3 -cclib -lcamlidl -cclib -lz3stubs z3.cmx -o z3.cmxa

ocamlmktop -o ocamlz3 z3.cma -ccopt -L. -cclib -lz3 -cclib -lcamlidl

rm z3.cm{o,x} *.o
