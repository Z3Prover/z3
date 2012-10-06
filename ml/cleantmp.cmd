@echo off

REM Script to delete intermediate temporary files from generating Z3 OCaml API

REM files produced by generate_mlapi.cmd
del /q 2>NUL z3_api.idl

REM files produced by compile_mlapi.cmd
del /q 2>NUL *.cmi *.cmo *.cmx *.cma *.cmxa *.obj *.lib *.pdb ocamlz3.exe

REM files produced by test_mlapi.cmd
del /q 2>NUL test*.exe queen*.exe test_*api.out test_*apiV3.out test_*api.err test_*apiV3.err queen.out queen.err z3.log ml.log test_mlapi.log .z3-trace

REM backup files
del /q 2>NUL *~
