#!/bin/bash

ocamlc -o test_mlapi.byte -I ../../ocaml/ z3.cma test_mlapi.ml
ocamlopt -o test_mlapi -I ../../ocaml/ z3.cmxa test_mlapi.ml

rm *.cm{i,o,x} *.o
