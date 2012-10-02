@echo off

REM Script to delete generated Z3 OCaml API files

call .\cleantmp.cmd

REM files produced by generate_mlapi.cmd
del /q 2>NUL z3_stubs.c z3.mli z3.ml z3V3_stubs.*.c z3V3.*.mli z3V3.*.ml

REM files produced by update-ml-doc.cmd
rd 2>NUL /s /q doc

exit /B 0
